// ==UserScript==
// @name         QQ Mail 附件批量下载
// @description  批量下载QQ邮箱附件，提取全部附件，智能分类命名
// @version      3.4.0
// @author       XHXIAIEIN
// @namespace    https://greasyfork.org/zh-CN/scripts/535160
// @supportURL   https://github.com/xhxiaiein/Auto-Download-QQMail-Attach
// @match        https://wx.mail.qq.com/*
// @grant        none
// @run-at       document-idle
// ==/UserScript==

(function () {
	'use strict';

	// ============================================================
	//  用户配置
	// ============================================================

	const SCAN_SUBFOLDERS = true; // 扫描已下载时是否递归子目录
	const CONCURRENCY = 10; // 并发下载数

	// 落盘目录组织方式
	//   'type'        默认。按文件类型一级分类：图片/、文档/、视频/...
	//   'subject'     按邮件主题
	//   'sender'      按发件人昵称（缺省回退到邮箱 local-part）
	//   'email'       按完整发件人邮箱地址
	//   'pinyin'      按发件人 pinyin 首字母：A-Z / 0-9 / _其他
	//   'time-month'  按月：YYYY-MM
	//   'time-week'   按周：YYYY-Www
	//   'time-day'    按日：YYYY-MM-DD
	//   'time-hour'   按小时：YYYY-MM-DD-HH
	//   'time-period' 按时段：YYYY-MM-DD-上午/下午/晚上（5/12/18 三段）
	const SAVE_MODE = 'type';

	// QQ 邮箱标签 ID（按需启用）。默认 null = 不打。
	// 启用：邮箱里建标签 → 打开它 → 把 URL 里的 tagid 填进来。填错或不存在会自动跳过。
	const TAG_NO_ATTACH = null;
	const TAG_READ = null;
	const TAG_DOWNLOADED = null;
	const TAG_DUPLICATE = null;

	// ============================================================
	//  Constants
	// ============================================================

	const DIR_IMAGE = '图片';
	const DIR_INLINE = '内嵌图片';
	const DIR_PROJECT = '项目文件';
	const DIR_DOC = '文档';
	const DIR_AUDIO = '音频';
	const DIR_VIDEO = '视频';
	const DIR_ARCHIVE = '压缩文件';
	const DIR_DUP = '重复';
	const DIR_OTHER = '其他';
	const DIR_MANUAL = '转人工';

	// ============================================================
	//  State
	// ============================================================

	let db = null;
	let rootHandle = null;
	let engineRunning = false;
	let sid = null;
	let folderId = null;
	let folderName = '';
	let identityMap = new Map();
	let mailMap = {};
	let addrMap = new Map();

	// ============================================================
	//  Utilities
	// ============================================================

	function getSidFromUrl() {
		const m = location.href.match(/sid=([^&#]+)/);
		return m ? m[1] : null;
	}

	function getFolderIdFromUrl() {
		const m = location.href.match(/#\/list\/(\d+)/);
		return m ? parseInt(m[1]) : null;
	}

	// MutationObserver-based wait. The previous setInterval(250ms, 5s) was too short for
	// QQ Mail's first paint when the user lands directly on a folder URL — `.mail_app`
	// can take 6-10s to render, so the panel silently failed to mount until the user
	// switched folders (which re-triggered init after the DOM had stabilized). 30s
	// timeout + observer reacts the moment the node appears.
	function waitForSelector(selector, timeout = 30000) {
		return new Promise(resolve => {
			const initial = document.querySelector(selector);
			if (initial) return resolve(initial);
			let settled = false;
			const finish = (val, observer, timer) => {
				if (settled) return;
				settled = true;
				observer.disconnect();
				clearTimeout(timer);
				resolve(val);
			};
			const observer = new MutationObserver(() => {
				const el = document.querySelector(selector);
				if (el) finish(el, observer, timer);
			});
			observer.observe(document.documentElement, { childList: true, subtree: true });
			const timer = setTimeout(() => finish(null, observer, timer), timeout);
		});
	}

	// Filename sanitizer for cross-platform FS writes (NTFS / APFS / ext4 via FSA).
	// Beyond the obvious reserved char list, three Windows footguns matter:
	//   - control chars (\x00-\x1F) inside a mail subject silently fail getFileHandle
	//   - trailing dots / spaces are stripped silently → file created != name asked for
	//   - device names (CON, PRN, NUL, COM1-9, LPT1-9) are reserved with or without ext
	// NFC normalization keeps QQ-side NFC and macOS NFD entries dedup-equivalent.
	function sanitizeFilename(name) {
		let s = String(name ?? '')
			.normalize('NFC')
			.replace(/[<>:"|?*\/\\]/g, '_')
			.replace(/[\x00-\x1F\x7F]/g, '');
		s = s.replace(/^\s+/, '').replace(/[.\s]+$/, '');

		const MAX = 200;
		if (s.length > MAX) {
			const dot = s.lastIndexOf('.');
			const extLen = dot > 0 && s.length - dot <= 12 ? s.length - dot : 0;
			let cut = MAX - extLen;
			// Don't strand a high surrogate without its low counterpart.
			const cu = s.charCodeAt(cut - 1);
			if (cu >= 0xd800 && cu <= 0xdbff) cut--;
			s = s.slice(0, cut) + (extLen ? s.slice(s.length - extLen) : '');
		}

		if (/^(con|prn|aux|nul|com[1-9]|lpt[1-9])(\.|$)/i.test(s)) s = '_' + s;
		return s || 'unnamed';
	}

	// 相机/IM 自动生成名（微信图片_xxx、mmexport_xxx、IMG_xxx、Screenshot_xxx、DSC_xxx
	// 等）内容无关——时间戳/序号每次转发都会变，且同一发件人重复出现的同型名几乎都是
	// 不同作品，因此直接跳出 dedup，让普通的同名碰撞重命名（` (2)`）兜底盘上冲突。
	const AUTO_NAME_PATTERNS = [/^微信图片_[\d_]+\.[A-Za-z0-9]+$/, /^QQ图片\d+\.[A-Za-z0-9]+$/, /^mmexport\d+\.[A-Za-z0-9]+$/i, /^IMG[-_]\d[\d_]*\.[A-Za-z0-9]+$/i, /^Screenshot[-_]?\d[\d\-_:.\s]*\.[A-Za-z0-9]+$/i, /^(DSC|DSCN|DSCF)\d+\.[A-Za-z0-9]+$/i];
	function isAutoGenNfcName(nfcName) {
		return AUTO_NAME_PATTERNS.some(re => re.test(nfcName));
	}

	// QQ 邮件接口里的时间多为秒级 unix 时间戳；ts 是 0/undefined 时返回空串方便表格直接拼接。
	function fmtDatetime(ts) {
		if (!ts) return '';
		const d = new Date(ts * 1000);
		const pad = n => String(n).padStart(2, '0');
		return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}`;
	}

	// HTML-escape before writing to innerHTML. Mail subject / sender nick / attachment name
	// are attacker-controlled: a subject like `<img src=x onerror=...>` would execute in the
	// wx.mail.qq.com origin, where this script has full session access.
	function escapeHtml(s) {
		return String(s ?? '')
			.replace(/&/g, '&amp;')
			.replace(/</g, '&lt;')
			.replace(/>/g, '&gt;')
			.replace(/"/g, '&quot;')
			.replace(/'/g, '&#39;');
	}

	// Escape for markdown table cells: pipe would break table structure, newline would split row.
	function escapeMd(s) {
		return String(s ?? '')
			.replace(/\|/g, '\\|')
			.replace(/\r?\n/g, ' ');
	}

	// Truncate by Unicode code point, not UTF-16 code unit. String.slice cuts surrogate
	// pairs in half — an emoji or CJK Extension B char at the boundary becomes a lone
	// surrogate that renders as � in the markdown report.
	function truncate(s, n) {
		const arr = [...(s ?? '')];
		return arr.length <= n ? String(s ?? '') : arr.slice(0, n).join('') + '…';
	}

	// A "convention-compliant" filename has 6+ consecutive digits (QQ/phone) with clean boundaries
	// on both sides — separator / CJK / edge / QQ-prefix marker. This rejects digit runs embedded
	// in hex/hash strings like "6992751ddbd0..." that would otherwise pollute identity extraction.
	const CONV_BOUNDARY_RE = /[-_\s+·()（）【】\[\]、，\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaffQqＱｑ]/;
	const CONV_TRAIL_SEP_RE = /[-_\s+·]/;

	function isConventionBoundary(ch) {
		if (ch === '') return true;
		// Surrogate pair returned by getBoundaryChar — emoji or CJK Extension B+ char.
		// Neither can be part of a digit run, so treat as a non-alphanumeric boundary.
		if (ch.length === 2) return true;
		return CONV_BOUNDARY_RE.test(ch);
	}

	// Read the char at position i as a full Unicode scalar. Bare s[i] returns one
	// UTF-16 code unit, so an emoji (or CJK Ext B+ char) sitting against a digit run
	// gives back an orphan low/high surrogate that fails the boundary test, dropping
	// otherwise-valid QQ numbers like "🎨123456".
	function getBoundaryChar(s, i) {
		if (i < 0 || i >= s.length) return '';
		const cu = s.charCodeAt(i);
		if (cu >= 0xdc00 && cu <= 0xdfff && i > 0) return s.slice(i - 1, i + 1);
		if (cu >= 0xd800 && cu <= 0xdbff && i + 1 < s.length) return s.slice(i, i + 2);
		return s[i];
	}

	function findBoundedDigitRuns(s, re) {
		const runs = [];
		re.lastIndex = 0;
		let m;
		while ((m = re.exec(s)) !== null) {
			const start = m.index;
			const end = start + m[0].length;
			const before = getBoundaryChar(s, start - 1);
			const after = getBoundaryChar(s, end);
			if (isConventionBoundary(before) && isConventionBoundary(after) && !isTimestampDigitRun(m[0])) {
				runs.push({ start, end, text: m[0] });
			}
		}
		return runs;
	}

	function hasConventionDigits(s) {
		return findBoundedDigitRuns(s, /\d{6,}/g).length > 0;
	}

	function extractConventionPrefix(s) {
		const runs = findBoundedDigitRuns(s, /\d{6,}/g);
		if (runs.length === 0) return null;
		let end = runs[runs.length - 1].end;
		if (end < s.length && CONV_TRAIL_SEP_RE.test(s[end])) end++;
		return s.slice(0, end);
	}

	function getAttachments(mail) {
		return [...(mail.normal_attach || []), ...(mail.cloud_attach || [])];
	}

	function hasAttachments(mail) {
		return (mail.normal_attach?.length || 0) + (mail.cloud_attach?.length || 0) > 0;
	}

	function getSenderEmail(mail) {
		return mail.senders?.item?.[0]?.email || '';
	}

	function getSenderNick(mail) {
		return mail.senders?.item?.[0]?.nick || '';
	}

	function buildIdentitySegs(identity) {
		const s = [];
		if (identity.parsedName) s.push(identity.parsedName);
		if (identity.qq) s.push(identity.qq);
		if (identity.phone) s.push(identity.phone);
		if (s.length === 0) {
			// 标题/附件/AI/搜索都没解析到身份字段 — 用发件人显示名 + 邮箱 local-part
			// 兜底，让文件名至少能区分发件人。
			if (identity.nick) s.push(identity.nick);
			if (identity.email) {
				const local = identity.email.split('@')[0];
				if (local && local !== identity.nick) s.push(local);
			}
		}
		return s;
	}

	async function batchParallel(items, concurrency, fn) {
		for (let i = 0; i < items.length; i += concurrency) {
			await Promise.all(items.slice(i, i + concurrency).map(fn));
		}
	}

	function ensureAbsoluteUrl(url) {
		if (url.startsWith('/')) url = 'https://wx.mail.qq.com' + url;
		if (!url.includes('sid=')) url += (url.includes('?') ? '&' : '?') + 'sid=' + sid;
		return url;
	}

	function replaceSid(url, newSid) {
		return url.replace(/sid=[^&]+/, 'sid=' + newSid);
	}

	// Filter out date-like digit strings (YYYYMMDD, YYMMDD) that otherwise look like QQ numbers.
	// Accepts 19xx/20xx so it doesn't silently break in 2030.
	const DATE8_RE = /^(?:19|20)\d{2}(?:0[1-9]|1[0-2])(?:0[1-9]|[12]\d|3[01])$/;
	const DATE6_RE = /^\d{2}(?:0[1-9]|1[0-2])(?:0[1-9]|[12]\d|3[01])$/;
	// HHMMSS — for camera filenames like IMG_<date>_<time>, the trailing 6 digits are a
	// timestamp not an identity. Without this, IMG_20260307_145804.jpg gets treated as
	// already conventional and skips sender-prefix renaming.
	const TIME6_RE = /^(?:[01]\d|2[0-3])[0-5]\d[0-5]\d$/;
	// 13-digit Unix ms timestamps (~2014–2033). Matches WeChat/QQ camera dumps like
	// mmexport1709870404123.jpg without colliding with 11-digit phone numbers.
	const TS13_RE = /^1[3-9]\d{11}$/;
	function isTimestampDigitRun(text) {
		const len = text.length;
		if (len === 8) return DATE8_RE.test(text);
		if (len === 6) return DATE6_RE.test(text) || TIME6_RE.test(text);
		if (len === 13) return TS13_RE.test(text);
		return false;
	}
	function cleanQQs(qqs) {
		return qqs.filter(q => {
			if (DATE8_RE.test(q)) return false;
			if (q.length < 5) return false;
			if (q.length === 6 && DATE6_RE.test(q)) return false;
			return true;
		});
	}

	// ============================================================
	//  IndexedDB
	// ============================================================

	const DB_NAME = 'mail_downloader_db';
	const DB_VERSION = 30000;

	function openDB() {
		return new Promise((resolve, reject) => {
			const req = indexedDB.open(DB_NAME, DB_VERSION);
			req.onupgradeneeded = e => {
				const d = e.target.result;
				if (!d.objectStoreNames.contains('tasks')) d.createObjectStore('tasks', { keyPath: 'id' });
				if (!d.objectStoreNames.contains('meta')) d.createObjectStore('meta', { keyPath: 'key' });
			};
			req.onsuccess = () => resolve(req.result);
			req.onerror = () => reject(req.error);
		});
	}

	function dbPut(store, data) {
		return new Promise((resolve, reject) => {
			const tx = db.transaction(store, 'readwrite');
			tx.objectStore(store).put(data);
			tx.oncomplete = () => resolve();
			tx.onerror = () => reject(tx.error);
		});
	}

	function dbGetAll(store) {
		return new Promise((resolve, reject) => {
			const tx = db.transaction(store, 'readonly');
			const req = tx.objectStore(store).getAll();
			req.onsuccess = () => resolve(req.result);
			tx.onerror = () => reject(tx.error);
		});
	}

	function dbPutBatch(store, items) {
		return new Promise((resolve, reject) => {
			const tx = db.transaction(store, 'readwrite');
			const s = tx.objectStore(store);
			for (const item of items) s.put(item);
			tx.oncomplete = () => resolve();
			tx.onerror = () => reject(tx.error);
		});
	}

	async function dbDeleteByFolder(targetFolderId) {
		const all = await dbGetAll('tasks');
		const toDelete = all.filter(t => t.folderId === targetFolderId);
		if (toDelete.length === 0) return;
		return new Promise((resolve, reject) => {
			const tx = db.transaction('tasks', 'readwrite');
			const store = tx.objectStore('tasks');
			for (const t of toDelete) store.delete(t.id);
			tx.oncomplete = () => resolve();
			tx.onerror = () => reject(tx.error);
		});
	}

	// ============================================================
	//  QQ Mail API
	// ============================================================

	function rnd() {
		return Math.random().toString().slice(2) + Date.now();
	}

	function apiGet(path) {
		const sep = path.includes('?') ? '&' : '?';
		return fetch(path + sep + 'r=' + rnd(), { credentials: 'include' }).then(r => r.json());
	}

	function apiPost(path, params) {
		params.r = rnd();
		params.sid = sid;
		return fetch(path, {
			method: 'POST',
			credentials: 'include',
			headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
			body: new URLSearchParams(params).toString(),
		}).then(r => r.json());
	}

	async function verifySession() {
		const data = await apiGet(`/list/folderlist?sid=${sid}`);
		return data.head.ret === 0 ? data : null;
	}

	async function fetchMailList(page) {
		const url = `/list/maillist?sid=${sid}&dir=${folderId}&dirid=${folderId}&func=1&sort_type=1&sort_direction=1&page_now=${page}&page_size=50`;
		const data = await apiGet(url);
		if (data.head.ret !== 0) throw new Error(`API ret=${data.head.ret}: ${data.head.msg || data.head.stack || ''}`);
		return data.body;
	}

	async function fetchReadMail(mailId) {
		const data = await apiGet(`/read/readmail?sid=${sid}&mailid=${mailId}&func=1`);
		return data;
	}

	// Global mailbox-wide search. We use it to harvest identity tokens (QQ / phone /
	// name) from a sender's historical subjects when the currently downloaded mails
	// don't carry the standard "name+qq+phone+work" pattern.
	async function fetchSearchByKeyword(keyword, pageSize = 50) {
		const data = await apiPost('/list/search', { page_now: 0, page_size: pageSize, keyword });
		if (data.head?.ret !== 0) return [];
		return data.body?.list || [];
	}

	async function markMailRead(mailId) {
		return apiPost('/mgr/mailmgr', { func: 4, mailid: mailId, folderid: folderId, choose_type: 1 });
	}

	// 未配置 (null) → 静默跳过。
	// 配置了但服务端首次返回非 0 (tagid 不存在 / 被删 / 无权限) → 拉黑本会话后续同 id 调用。
	// 网络异常不入黑名单（可能只是临时抖动），由调用方的 .catch 兜住。
	const failedTagIds = new Set();
	async function addTag(mailId, tagId) {
		if (tagId == null) return;
		if (failedTagIds.has(tagId)) return;
		const r = await apiPost('/mgr/mailmgr', { func: 12, mailid: mailId, tagid: tagId, folderid: folderId, choose_type: 1 });
		if (r?.head?.ret !== 0) {
			failedTagIds.add(tagId);
		}
	}

	async function addTags(mailId, tagIds) {
		await Promise.all(tagIds.map(t => addTag(mailId, t)));
	}

	// 仅当用户配置了 TAG_DUPLICATE 时才打标，重复方邮件按 mailid 去重。
	async function tagDuplicateMails(tasks, onProgress) {
		if (TAG_DUPLICATE == null) return;
		const dupMails = [...new Set(tasks.filter(t => (t.category || t.dir) === DIR_DUP && t.status === 'done').map(t => t.mailid))];
		if (dupMails.length === 0) return;
		onProgress?.(dupMails.length);
		await batchParallel(dupMails, 10, mid => addTag(mid, TAG_DUPLICATE).catch(() => {}));
	}

	async function pollAsyncTask(taskId) {
		for (let i = 0; i < 60; i++) {
			const r = await apiPost('/mgr/mailmgr', { func: 26, async_task_func: 1, async_taskid: taskId });
			if (r.head.ret !== 0) return false;
			if (!r.body?.is_async) return true;
			await new Promise(resolve => setTimeout(resolve, 500));
		}
		return false;
	}

	async function markAllUnread() {
		const r = await apiPost('/mgr/mailmgr', { func: 5, folderid: folderId, choose_type: 2 });
		if (r.head.ret !== 0) return false;
		if (r.body?.is_async && r.body?.async_taskid) {
			return pollAsyncTask(r.body.async_taskid);
		}
		return true;
	}

	// QQ Mail's contact book carries pre-computed pinyin (`quanpin`) and initials
	// (`jianpin`) for every contact. We use them as ASCII identity tokens in
	// manifest keys so the file index stays tool-friendly even when the on-disk
	// Chinese folder/filename gets renamed.
	async function fetchAddrList() {
		try {
			const data = await apiGet(`/addr/addrlist?sid=${sid}`);
			if (data?.head?.ret !== 0) return new Map();
			const items = data.body?.addr_list?.items || [];
			const map = new Map();
			for (const item of items) {
				const mails = item.mail || [];
				for (const m of mails) {
					if (!m) continue;
					map.set(m.toLowerCase(), {
						quanpin: item.quanpin || '',
						jianpin: item.jianpin || '',
						remark: item.remark || '',
					});
				}
			}
			return map;
		} catch {
			return new Map();
		}
	}

	function getQuanpin(email) {
		if (!email) return 'unknown';
		const info = addrMap.get(email.toLowerCase());
		if (info?.quanpin) return info.quanpin;
		if (info?.jianpin) return info.jianpin;
		// Final fallback: email local-part. QQ-numeric mailboxes get a `qq` prefix
		// so the token reads like an identity rather than a bare number.
		const local = (email.split('@')[0] || '').toLowerCase();
		if (!local) return 'unknown';
		return /^\d+$/.test(local) ? `qq${local}` : local;
	}

	// 发件人 pinyin 首字母分类的入口；非字母数字（含直接以中文备注开头）落入 _其他。
	function getPinyinInitial(email) {
		const info = addrMap.get((email || '').toLowerCase());
		let src = info?.jianpin || info?.quanpin || '';
		if (!src) src = (email || '').split('@')[0] || '';
		const c = (src.charAt(0) || '').toUpperCase();
		if (/[A-Z0-9]/.test(c)) return c;
		return '_其他';
	}

	function getTimePeriod(hour) {
		if (hour >= 5 && hour < 12) return '上午';
		if (hour >= 12 && hour < 18) return '下午';
		return '晚上';
	}

	// ISO-8601 周序，跨年时归属遵守 ISO 规则（不是简单的 dayOfYear/7）。
	function getIsoWeek(date) {
		const d = new Date(Date.UTC(date.getFullYear(), date.getMonth(), date.getDate()));
		const day = d.getUTCDay() || 7;
		d.setUTCDate(d.getUTCDate() + 4 - day);
		const yearStart = new Date(Date.UTC(d.getUTCFullYear(), 0, 1));
		const weekNo = Math.ceil(((d - yearStart) / 86400000 + 1) / 7);
		return { year: d.getUTCFullYear(), week: weekNo };
	}

	// 给定 task 的发件人/邮件信息算出当前 SAVE_MODE 下对应的 bucket。返回 null 表示
	// 当前模式无 bucket（'type' / null / 未识别值），调用方回退到 category（平铺）。
	const TIME_MODES = new Set(['time-month', 'time-week', 'time-day', 'time-hour', 'time-period']);
	function computeSaveBucket(taskLite, mailInfo) {
		const mode = SAVE_MODE;
		if (mode === 'subject') {
			const s = sanitizeFilename(mailInfo?.subject || '');
			return s || '_无主题';
		}
		if (mode === 'sender') {
			const nick = mailInfo?.senderNick || '';
			const email = taskLite?.email || mailInfo?.senderEmail || '';
			const name = nick || email.split('@')[0] || '';
			const s = sanitizeFilename(name);
			return s || '_未知发件人';
		}
		if (mode === 'email') {
			const email = taskLite?.email || mailInfo?.senderEmail || '';
			const s = sanitizeFilename(email);
			return s || '_未知邮箱';
		}
		if (mode === 'pinyin') {
			return getPinyinInitial(taskLite?.email || mailInfo?.senderEmail || '');
		}
		if (TIME_MODES.has(mode)) {
			const ts = mailInfo?.totime;
			if (!ts) return '_未知时间';
			const d = new Date(ts * 1000);
			const pad = n => String(n).padStart(2, '0');
			const y = d.getFullYear();
			const m = pad(d.getMonth() + 1);
			const day = pad(d.getDate());
			const h = pad(d.getHours());
			if (mode === 'time-month') return `${y}-${m}`;
			if (mode === 'time-week') {
				const w = getIsoWeek(d);
				return `${w.year}-W${String(w.week).padStart(2, '0')}`;
			}
			if (mode === 'time-day') return `${y}-${m}-${day}`;
			if (mode === 'time-hour') return `${y}-${m}-${day}-${h}`;
			return `${y}-${m}-${day}-${getTimePeriod(d.getHours())}`;
		}
		return null; // 'type' / null / 未识别值 → 回退平铺
	}

	// 把分类（文件类型）与 SAVE_MODE 决定的 bucket 合并成落盘相对路径。
	// 重复/、转人工/ 始终保留为顶层目录，便于人工审核；其它分类被 bucket 替换。
	function resolveSaveDir(category, taskLite, mailInfo) {
		const bucket = computeSaveBucket(taskLite, mailInfo);
		if (!bucket) return category;
		if (category === DIR_DUP || category === DIR_MANUAL) {
			return `${category}/${bucket}`;
		}
		return bucket;
	}

	// FSA 的 getDirectoryHandle 只接受单段 name，含 '/' 的相对路径需要逐级解析。
	async function resolveDirHandle(root, relPath, { create }) {
		const parts = String(relPath || '')
			.split('/')
			.filter(Boolean);
		let cur = root;
		for (const p of parts) {
			cur = await cur.getDirectoryHandle(p, { create });
		}
		return cur;
	}

	// manifest 键用的 ASCII 类型，独立于可被重命名的中文目录。
	const DIR_TO_TYPE = {
		[DIR_IMAGE]: 'image',
		[DIR_INLINE]: 'inline',
		[DIR_PROJECT]: 'project',
		[DIR_DOC]: 'doc',
		[DIR_AUDIO]: 'audio',
		[DIR_VIDEO]: 'video',
		[DIR_ARCHIVE]: 'archive',
		[DIR_DUP]: 'dup',
		[DIR_OTHER]: 'other',
		[DIR_MANUAL]: 'manual',
	};

	function buildManifestKey(entry) {
		// 优先 category（与 SAVE_MODE 解耦的稳定类型），缺失时回退 dir 兼容旧 DB 任务。
		const cat = entry.category || entry.dir;
		const type = DIR_TO_TYPE[cat] || 'other';
		const quanpin = entry.quanpin || getQuanpin(entry.email);
		return `${type}_${quanpin}_${entry.mailid}_${entry.fileid}`;
	}

	// ============================================================
	//  Phase 2: Scan mails
	// ============================================================

	async function scanAllMails(totalNum, onProgress) {
		const totalPages = Math.ceil(totalNum / 50);
		const allMails = [];

		for (let i = 0; i < totalPages; i += 3) {
			const batch = [];
			for (let j = i; j < Math.min(i + 3, totalPages); j++) {
				batch.push(fetchMailList(j));
			}
			const results = await Promise.all(batch);
			for (const body of results) {
				if (body.list) allMails.push(...body.list);
			}
			onProgress?.(allMails.length, totalNum);
		}

		return allMails;
	}

	// ============================================================
	//  Phase 3: Build identity map
	// ============================================================

	function extractPhoneQQ(text, id) {
		for (const r of findBoundedDigitRuns(text, /1[3-9]\d{9}/g)) id.phones.add(r.text);
		for (const r of findBoundedDigitRuns(text, /(?<!\d)[1-9]\d{4,10}(?!\d)/g)) {
			if (!/^1[3-9]\d{9}$/.test(r.text)) id.qqs.add(r.text);
		}
	}

	function ensureIdentity(email) {
		if (!identityMap.has(email)) {
			identityMap.set(email, { names: new Set(), qqs: new Set(), phones: new Set(), nicks: new Set() });
		}
		return identityMap.get(email);
	}

	// Pull every identity-like token (name candidate, QQ, phone) out of a single
	// subject string and merge it into the given id record. Shared between the
	// initial buildIdentityMap pass and the search-enrichment fallback so the
	// extraction rules stay in one place.
	function applySubjectToIdentity(id, subject) {
		if (!subject) return;
		const parts = subject.split(/[+＋]/);
		if (parts.length >= 4) id.names.add(parts[2].trim());
		for (const p of parts) extractPhoneQQ(p, id);
	}

	// 把 AI 解析结果按 name/qq/phone 各自的合规闸门写回 id；返回 {name, qq, phone, work}
	// 表示真正被接收的字段。AI 主题解析与搜索补全两条路径共用，保证字段闸规则只在一处。
	function applyParsedToIdentity(id, parsed) {
		const accepted = { name: '', qq: '', phone: '', work: parsed.work || '' };
		if (looksLikePersonName(parsed.name)) {
			id.names.add(parsed.name);
			accepted.name = parsed.name;
		}
		if (parsed.qq && /^\d{5,11}$/.test(parsed.qq)) {
			id.qqs.add(parsed.qq);
			accepted.qq = parsed.qq;
		}
		if (parsed.phone && /^1[3-9]\d{9}$/.test(parsed.phone)) {
			id.phones.add(parsed.phone);
			accepted.phone = parsed.phone;
		}
		return accepted;
	}

	// Accepts both attach_list entries and legacy mail objects.
	function buildIdentityMap(items) {
		identityMap = new Map();
		for (const item of items) {
			const email = item.sender?.addr || getSenderEmail(item);
			const nick = item.sender?.name || getSenderNick(item);
			if (!email) continue;

			const id = ensureIdentity(email);
			if (nick) id.nicks.add(nick);

			applySubjectToIdentity(id, item.subject || '');

			const eqq = email.match(/^(\d{5,11})@qq\.com$/);
			if (eqq) id.qqs.add(eqq[1]);

			if (item.name) extractPhoneQQ(item.name, id);
			if (item.normal_attach || item.cloud_attach) {
				for (const a of getAttachments(item)) {
					if (a.name) extractPhoneQQ(a.name, id);
				}
			}
		}
	}

	function getIdentity(email) {
		const id = identityMap.get(email);
		if (!id) return { name: '', parsedName: '', qq: '', phone: '', nick: '', email: email || '' };
		const pickNonDigit = set => [...set].find(n => n && !/^\d+$/.test(n)) || '';
		const parsedName = pickNonDigit(id.names);
		const nick = pickNonDigit(id.nicks);
		return {
			// `name` 保持原有 nick-fallback 行为，供 UI/report 等外部消费者使用；
			// 文件名构造请用 `parsedName`，只在 `buildIdentitySegs` 内决定何时回退到 nick + email。
			name: parsedName || nick || '',
			parsedName,
			qq: cleanQQs([...id.qqs])[0] || '',
			phone: [...id.phones][0] || '',
			nick,
			email: email || '',
		};
	}

	// ============================================================
	//  Phase 3a: Chrome Built-in AI enhancement
	// ============================================================

	let aiSession = null;
	let aiAvailable = false;

	async function initBuiltinAI() {
		try {
			if (!window.LanguageModel) return false;
			const caps = await window.LanguageModel.availability();
			if (caps === 'unavailable') return false;
			aiSession = await window.LanguageModel.create({
				expectedInputs: [{ type: 'text', languages: ['zh', 'en'] }],
				expectedOutputs: [{ type: 'text', languages: ['en'] }],
				systemPrompt: [
					'<role>',
					'You are a deterministic field extractor for photo-contest submission email subjects. Output is parsed downstream as JSON to build identity-keyed filenames, so token-classification accuracy is critical.',
					'</role>',
					'',
					'<output_schema>',
					'Return JSON: {"name":"","qq":"","phone":"","work":""}',
					"- name:  submitter's personal handle (a real person — 2–4 Chinese chars or short English alias). Empty if absent.",
					'- qq:    5–11 digits, NOT an 11-digit mobile. Empty if absent.',
					'- phone: 11 digits starting with 1[3-9]. Empty if absent.',
					'- work:  title of the submitted work. Empty if absent.',
					'</output_schema>',
					'',
					'<parsing_procedure>',
					'1. Split the subject into tokens. Separators commonly co-occur and include:',
					'     -   _   +   ＋   ➕   |   /   \\   ·   、   ,   ，   ;   ；   :   ：   space   tab',
					'2. For each token, strip a leading "Q" or "QQ" if it precedes digits.',
					'3. Classify by shape:',
					'   • 11 digits starting with 1[3-9]  →  phone',
					'   • 5–11 digits (not a phone)       →  qq',
					'   • Short text (≤6 chars), contains no digits, not blocklisted  →  candidate name',
					'   • Anything else (digits inside, >6 chars, or blocklisted)     →  contest / work / noise — NEVER name',
					'4. Pick exactly ONE name token. If multiple candidates exist, prefer the one positioned between the contest token and the QQ/phone tokens.',
					'5. Any remaining descriptive token (typically the trailing one) goes to work.',
					'</parsing_procedure>',
					'',
					'<name_blocklist>',
					'A token is NEVER `name` if it contains any of: 大赛 / 比赛 / 赛事 / 活动 / 征集. These are contest/event labels.',
					'</name_blocklist>',
					'',
					'<why_this_matters>',
					"A wrong `name` (e.g. a contest title leaking into the field) collapses every submitter's filename to the same prefix and corrupts the local index. When uncertain, leave `name` empty — empty is safe; wrong is destructive.",
					'</why_this_matters>',
				].join('\n'),
			});
			aiAvailable = true;
			return true;
		} catch (e) {
			return false;
		}
	}

	// Reject AI-returned names that are clearly not personal names — competition/activity titles
	// otherwise pollute identityMap and every filename prefix collapses to the same value.
	const NAME_BLOCKLIST_RE = /(大赛|比赛)/;
	function looksLikePersonName(s) {
		if (!s) return false;
		if (s.length > 6) return false;
		if (/\d/.test(s)) return false;
		if (NAME_BLOCKLIST_RE.test(s)) return false;
		return true;
	}

	async function aiParseSubject(subject) {
		if (!aiSession || !subject) return null;
		const prompt = [
			'<examples>',
			'<example>',
			'<subject>城市摄影大赛2026-张三-QQ12345-13800000001</subject>',
			'<output>{"name":"张三","qq":"12345","phone":"13800000001","work":""}</output>',
			'</example>',
			'<example>',
			'<subject>城市摄影大赛2026 小李 87654321 13900000002</subject>',
			'<output>{"name":"小李","qq":"87654321","phone":"13900000002","work":""}</output>',
			'</example>',
			'<example>',
			'<subject>投稿➕Alice➕Q1234567890➕18800000003➕山海</subject>',
			'<output>{"name":"Alice","qq":"1234567890","phone":"18800000003","work":"山海"}</output>',
			'</example>',
			'<example>',
			'<subject>城市摄影大赛2026_王五_QQ23456789_13700000004_夜色</subject>',
			'<output>{"name":"王五","qq":"23456789","phone":"13700000004","work":"夜色"}</output>',
			'</example>',
			'<example>',
			'<subject>城市摄影大赛2026+赵六+34567890+13600000005</subject>',
			'<output>{"name":"赵六","qq":"34567890","phone":"13600000005","work":""}</output>',
			'</example>',
			'<example label="no entrant identity — name must stay empty">',
			'<subject>城市摄影大赛2026投稿</subject>',
			'<output>{"name":"","qq":"","phone":"","work":""}</output>',
			'</example>',
			'</examples>',
			'',
			'Now extract from this subject. Output the JSON only.',
			`<subject>${subject}</subject>`,
			'<output>',
		].join('\n');
		try {
			const result = await aiSession.prompt(prompt, {
				responseConstraint: {
					type: 'object',
					properties: {
						name: { type: 'string' },
						qq: { type: 'string' },
						phone: { type: 'string' },
						work: { type: 'string' },
					},
					required: ['name', 'qq', 'phone', 'work'],
				},
			});
			return typeof result === 'string' ? JSON.parse(result) : result;
		} catch (e) {
			return null;
		}
	}

	async function enhanceIdentityWithAI(allMails, onProgress) {
		if (!aiAvailable) return { count: 0, items: [] };

		// Dedup at intake so the displayed denominator equals the actual LLM call count.
		// Without this, multiple mails from the same sender all inflate `needAI.length`
		// even though we only prompt the model once per sender.
		const needAI = [];
		const queued = new Set();
		for (const mail of allMails) {
			const email = mail.senders?.item?.[0]?.email;
			if (!email || queued.has(email)) continue;
			const id = identityMap.get(email);
			// id.aiTried is set by enrichIdentityFromSearch after it has already
			// invoked aiParseSubject on the richest historical subject — skipping
			// here avoids a redundant LLM call on a weaker local subject.
			if (id && id.names.size === 0 && !id.aiTried && mail.subject) {
				queued.add(email);
				needAI.push(mail);
			}
		}

		if (needAI.length === 0) return { count: 0, items: [] };

		// items: full record of every successful subject parse — surfaced in the panel
		// and report so the user can audit what the on-device LM actually pulled out.
		const items = [];
		for (let i = 0; i < needAI.length; i++) {
			const mail = needAI[i];
			const email = mail.senders?.item?.[0]?.email;

			onProgress?.(`AI 解析 ${i + 1}/${needAI.length}`);
			const parsed = await aiParseSubject(mail.subject);
			if (!parsed) continue;

			const id = identityMap.get(email);
			const accepted = applyParsedToIdentity(id, parsed);

			// Skip work-only rows — a parsed work title without any identity field
			// doesn't change the filename, so surfacing it in the panel only adds noise.
			if (accepted.name || accepted.qq || accepted.phone) {
				items.push({
					email,
					nick: mail.senders?.item?.[0]?.nick || '',
					subject: mail.subject,
					parsed: accepted,
				});
			}
		}

		// count = emails whose name field was filled — kept for backward compat with
		// downstream stats. items.length may be larger (qq-only / phone-only matches).
		const count = items.filter(it => it.parsed.name).length;
		return { count, items };
	}

	// Score subjects by how parser-friendly they look — most separator-delimited
	// tokens within a reasonable length window — so a single LLM call works on
	// the richest example rather than wasting it on a one-liner.
	function pickRichestSubject(subjects) {
		let best = null;
		let bestScore = -1;
		for (const s of subjects) {
			if (!s || s.length < 10 || s.length > 120) continue;
			const score = s.split(/[+＋\-_]/).length;
			if (score > bestScore) {
				bestScore = score;
				best = s;
			}
		}
		return best;
	}

	// Phase 3a-bis: for senders whose identity is still incomplete after the
	// local-subject pass, hit /list/search and harvest tokens from their
	// historical subjects. Regex-only as long as it pulls something useful;
	// only senders whose name still ends up empty fall back to a single AI
	// parse on the richest harvested subject. Runs in parallel with
	// initBuiltinAI — stage 2 awaits aiReadyPromise internally so the user
	// never sees a dedicated "search" step.
	async function enrichIdentityFromSearch(allMails, aiReadyPromise) {
		const targets = [];
		const seen = new Set();
		for (const mail of allMails) {
			const email = mail.senders?.item?.[0]?.email;
			if (!email || seen.has(email)) continue;
			seen.add(email);
			const cur = getIdentity(email);
			if (!cur.name || (!cur.qq && !cur.phone)) targets.push(email);
		}

		if (targets.length === 0) return { count: 0, items: [] };

		const harvest = new Map();
		await batchParallel(targets, 5, async email => {
			let mails;
			try {
				mails = await fetchSearchByKeyword(email);
			} catch (e) {
				mails = [];
			}
			if (mails.length === 0) return;

			const id = ensureIdentity(email);
			const subjects = [];
			let nick = '';
			for (const m of mails) {
				const n = m.senders?.item?.[0]?.nick;
				if (n) {
					id.nicks.add(n);
					if (!nick) nick = n;
				}
				const subject = m.subject || '';
				if (subject) {
					applySubjectToIdentity(id, subject);
					subjects.push(subject);
				}
			}
			harvest.set(email, { nick, subjects });
		});

		// AI 不可用时下面的 fuzzy 兜底直接跳过，仅返回 stage1 regex 的成果。
		const aiReady = aiReadyPromise ? await aiReadyPromise : aiAvailable;

		// Stage 2：仅 fuzzy hit（regex 拿到 qq/phone 但没名字）走 LLM，每发件人 1 次。
		const items = [];
		for (const email of targets) {
			const h = harvest.get(email);
			if (!h) continue;
			const before = getIdentity(email);
			let aiParsed = null;
			let aiSubject = '';
			if (!before.name && (before.qq || before.phone) && aiReady) {
				aiSubject = pickRichestSubject(h.subjects);
				if (aiSubject) {
					const id = ensureIdentity(email);
					id.aiTried = true;
					const parsed = await aiParseSubject(aiSubject);
					if (parsed) {
						applyParsedToIdentity(id, parsed);
						aiParsed = parsed;
					}
				}
			}

			const after = getIdentity(email);
			const improved = (after.name && !before.name) || (after.qq && !before.qq) || (after.phone && !before.phone);
			if (!improved) continue;

			items.push({
				email,
				nick: h.nick,
				subject: aiSubject || h.subjects[0] || '',
				parsed: {
					name: after.name,
					qq: after.qq,
					phone: after.phone,
					work: aiParsed?.work || '',
				},
				source: aiParsed ? 'search+ai' : 'search',
			});
		}

		const count = items.filter(it => it.parsed.name).length;
		return { count, items };
	}

	// ============================================================
	//  Phase 3b: Recalled mails + innerpiclist + tagging
	// ============================================================

	async function processRecalledMails(allMails, onProgress) {
		const recalled = [];
		const remaining = [];
		for (const m of allMails) {
			if ((m.subject || '').startsWith('发信方已撤回邮件：')) {
				recalled.push(m);
			} else {
				remaining.push(m);
			}
		}
		let tagged = 0;
		await batchParallel(recalled, 5, async m => {
			await addTags(m.emailid, [TAG_NO_ATTACH, TAG_READ]);
			onProgress?.(`处理已撤回 ${++tagged}/${recalled.length}`);
		});
		return { recalled, remaining };
	}

	async function processInnerPicList(noAttachMails, sendersWithAttach, onProgress) {
		const inlineEntries = [];
		const emptyMails = [];
		let processed = 0;

		async function processOne(mail, mailIdx) {
			try {
				const data = await fetchReadMail(mail.emailid);
				onProgress?.(`检查内嵌图片 ${++processed}/${noAttachMails.length}`);
				if (data.head?.ret !== 0) return;

				const picList = data.body?.item?.innerpiclist;
				if (!picList || picList.length === 0) {
					emptyMails.push(mail);
					await addTags(mail.emailid, [TAG_NO_ATTACH, TAG_READ]);
					return;
				}

				const senderEmail = getSenderEmail(mail);
				if (sendersWithAttach.has(senderEmail)) {
					await addTags(mail.emailid, [TAG_NO_ATTACH, TAG_READ]);
					return;
				}

				// Only TAG_NO_ATTACH here — TAG_DOWNLOADED is applied after all its inline pics download.
				await addTag(mail.emailid, TAG_NO_ATTACH);

				const identity = getIdentity(senderEmail);
				const idSegs = buildIdentitySegs(identity);
				// Identity-empty fallback: use sender's local-part so we never produce
				// nameless files. Last resort is mailIdx.
				const baseSegs = idSegs.length > 0 ? idSegs : [senderEmail.split('@')[0] || `mail${mailIdx}`];

				// SAVE_MODE-aware：在 'type' 模式下保留独立的 DIR_INLINE 目录，其他模式则与普通图片合并到 bucket。
				const inlineMailInfo = {
					subject: mail.subject || '',
					senderEmail,
					senderNick: getSenderNick(mail),
					totime: mail.totime,
				};
				const inlineDir = resolveSaveDir(DIR_INLINE, { email: senderEmail }, inlineMailInfo);

				for (let pi = 0; pi < picList.length; pi++) {
					const pic = picList[pi];
					let ext = 'jpg';
					// Match only the last extension so "photo.jpg.png" → "png", not "jpg".
					const nameMatch = (pic.name || '').match(/\.([a-zA-Z0-9]{2,5})$/);
					if (nameMatch) ext = nameMatch[1].toLowerCase();

					// Format: <name>-<qq>-<phone>-<picIdx>.<ext>, mirroring the dash-joined
					// convention used elsewhere. Cross-mail collisions (same identity, multiple
					// no-attach mails) are resolved by the dedup pass below.
					const filename = sanitizeFilename([...baseSegs, pi + 1].join('-') + '.' + ext);

					inlineEntries.push({
						url: ensureAbsoluteUrl(pic.downloadurl || ''),
						folderId,
						category: DIR_INLINE,
						dir: inlineDir,
						filename,
						mailid: mail.emailid,
						fileid: pic.fileid || `inline_${pi}`,
						fileIndex: pi + 1,
						email: senderEmail,
						quanpin: getQuanpin(senderEmail),
						origName: pic.name || '',
						size: pic.size || 0,
						isInline: true,
						senderEmail,
					});
				}
			} catch (e) {
				// swallow per-mail failures — inner-pic check is best-effort
			}
		}

		// mailIdx is only kept around as a synthetic fallback when sender local-part is missing.
		for (let i = 0; i < noAttachMails.length; i += 5) {
			const slice = noAttachMails.slice(i, i + 5);
			await Promise.all(slice.map((m, j) => processOne(m, i + j + 1)));
		}

		// Dedup within DIR_INLINE — same-identity senders mailing more than once would
		// otherwise produce identical "name-qq-phone-1.jpg" filenames and overwrite each
		// other on disk. Mirrors the (n) suffix scheme used in buildDownloadListFromAttach.
		const taken = new Set();
		const dirKey = (n, d) => `${d}/${n}`.toLowerCase();
		for (const entry of inlineEntries) {
			if (!taken.has(dirKey(entry.filename, entry.dir))) {
				taken.add(dirKey(entry.filename, entry.dir));
				continue;
			}
			const dot = entry.filename.lastIndexOf('.');
			const stem = dot > 0 ? entry.filename.slice(0, dot) : entry.filename;
			const ext = dot > 0 ? entry.filename.slice(dot) : '';
			let n = 2;
			let cand;
			do {
				cand = `${stem} (${n++})${ext}`;
			} while (taken.has(dirKey(cand, entry.dir)));
			entry.filename = cand;
			taken.add(dirKey(cand, entry.dir));
		}

		return { inlineEntries, emptyMails };
	}

	// ============================================================
	//  Phase 4: Build mail map + classify + generate download list
	// ============================================================

	function buildMailMapFromAttach(attachments) {
		mailMap = {};
		const byMail = new Map();
		for (const a of attachments) {
			if (!byMail.has(a.mailid)) byMail.set(a.mailid, []);
			byMail.get(a.mailid).push(a);
		}
		let mailIdx = 0;
		for (const [mid, items] of byMail) {
			mailIdx++;
			const first = items[0];
			mailMap[mid] = {
				subject: first.subject,
				senderEmail: first.sender?.addr || '',
				senderNick: first.sender?.name || '',
				attachCount: items.length,
				mailIdx,
				totime: first.ctime,
			};
			items.forEach((a, idx) => {
				mailMap[mid + '|' + a.fileid] = { attachIdx: idx + 1, attachTotal: items.length, origName: a.name };
			});
		}
	}

	function buildMailMap(allMails) {
		mailMap = {};
		let mailIdx = 0;
		for (const mail of allMails) {
			const attachAll = getAttachments(mail);
			const has = attachAll.length > 0;
			if (has) mailIdx++;
			mailMap[mail.emailid] = {
				subject: mail.subject,
				senderEmail: getSenderEmail(mail),
				senderNick: getSenderNick(mail),
				attachCount: attachAll.length,
				mailIdx: has ? mailIdx : 0,
				totime: mail.totime,
			};
			attachAll.forEach((a, idx) => {
				mailMap[mail.emailid + '|' + a.fileid] = { attachIdx: idx + 1, attachTotal: attachAll.length, origName: a.name };
			});
		}
	}

	const IMAGE_EXTS = new Set(['jpg', 'jpeg', 'png', 'webp', 'heic', 'heif', 'bmp', 'tiff', 'tif', 'raw', 'cr2', 'cr3', 'nef', 'arw', 'dng', 'orf', 'rw2', 'raf']);
	const PROJECT_EXTS = new Set(['psd', 'ai', 'sketch', 'fig', 'xd', 'cdr', 'eps', 'afdesign', 'afphoto', 'blend', 'c4d', 'max']);
	const DOC_EXTS = new Set(['pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'txt', 'rtf', 'csv', 'md', 'epub']);
	const AUDIO_EXTS = new Set(['mp3', 'wav', 'aac', 'flac', 'ogg', 'wma', 'm4a', 'ape', 'alac']);
	const VIDEO_EXTS = new Set(['mp4', 'mov', 'avi', 'mkv', 'wmv', 'flv', 'webm', 'mpg', 'mpeg', 'm4v', 'gif']);
	const ARCHIVE_EXTS = new Set(['zip', 'rar', '7z', 'gz', 'tar', 'bz2', 'xz', 'zst']);

	function classifyExt(ext) {
		if (ARCHIVE_EXTS.has(ext)) return DIR_ARCHIVE;
		if (IMAGE_EXTS.has(ext)) return DIR_IMAGE;
		if (PROJECT_EXTS.has(ext)) return DIR_PROJECT;
		if (DOC_EXTS.has(ext)) return DIR_DOC;
		if (AUDIO_EXTS.has(ext)) return DIR_AUDIO;
		if (VIDEO_EXTS.has(ext)) return DIR_VIDEO;
		return DIR_OTHER;
	}

	function buildDownloadListFromAttach(attachments) {
		// Duplicates keyed by sender_email + file_size + NFC-normalized filename; newest
		// (by ctime) wins within each group. Size alone overmatches — two unrelated JPGs
		// from the same sender can coincidentally share byte count (same camera/template),
		// so the name must match too. Auto-generated names (微信图片_xxx, mmexport, IMG_xxx,
		// Screenshot_xxx, DSC_xxx) are skipped entirely: their timestamp/sequence parts
		// vary on every re-share, and same-pattern names from one sender are usually
		// different works — name clashes get resolved by the collision-rename pass below.
		const ssMap = new Map();
		for (const a of attachments) {
			const nameKey = String(a.name || '').normalize('NFC');
			if (isAutoGenNfcName(nameKey)) continue;
			const k = `${a.sender?.addr || ''}_${a.size}_${nameKey}`;
			if (!ssMap.has(k)) ssMap.set(k, []);
			ssMap.get(k).push({ t: a.ctime, eid: a.mailid, fid: a.fileid });
		}
		const dupKeys = new Set();
		const dupGroupMap = new Map();
		const dupGroupInfo = new Map();
		for (const [groupKey, items] of ssMap) {
			if (items.length > 1) {
				items.sort((a, b) => b.t - a.t);
				const dups = items.slice(1);
				for (const item of items) dupGroupMap.set(`${item.eid}_${item.fid}`, groupKey);
				for (const it of dups) dupKeys.add(`${it.eid}_${it.fid}`);
				dupGroupInfo.set(groupKey, { kept: items[0], dups });
			}
		}

		// Trust the filename's last extension only when it's a known format.
		// - "photo.jpg.png" (a.type='jpg'): last ext 'png' is known → avoids double-ext "photo.jpg.png.jpg"
		// - "photo.2024.01.01" (a.type='jpg'): last ext '01' is unknown → fall back to a.type so the
		//   date-ish name doesn't get misclassified.
		function resolveStemExt(a) {
			const name = a.name || '';
			const lastDot = name.lastIndexOf('.');
			if (lastDot > 0 && lastDot < name.length - 1) {
				const nameExt = name.slice(lastDot + 1).toLowerCase();
				if (classifyExt(nameExt) !== DIR_OTHER) {
					return { stem: name.slice(0, lastDot), ext: nameExt };
				}
			}
			let ext = (a.type || '').toLowerCase();
			if (!ext && lastDot > 0) ext = name.slice(lastDot + 1).toLowerCase();
			let stem = name;
			if (ext && stem.toLowerCase().endsWith('.' + ext)) stem = stem.slice(0, -ext.length - 1);
			return { stem, ext };
		}

		// Most-common prefix per sender — tolerates one-off outliers if a sender has mixed naming.
		const senderPrefix = new Map();
		{
			const prefixCounts = new Map();
			for (const a of attachments) {
				const { stem } = resolveStemExt(a);
				const p = extractConventionPrefix(stem);
				if (!p) continue;
				const email = a.sender?.addr || '';
				let counts = prefixCounts.get(email);
				if (!counts) prefixCounts.set(email, (counts = new Map()));
				counts.set(p, (counts.get(p) || 0) + 1);
			}
			for (const [email, counts] of prefixCounts) {
				const [best] = [...counts.entries()].sort((x, y) => y[1] - x[1])[0];
				senderPrefix.set(email, best);
			}
		}

		const downloads = [];
		let id = 0;
		const perMailIdx = new Map();

		for (const a of attachments) {
			let { stem: origName, ext } = resolveStemExt(a);
			if (!ext) ext = 'jpg';

			const dk = `${a.mailid}_${a.fileid}`;
			const downloadHost = (() => {
				try {
					return new URL(a.download_url || '', 'https://wx.mail.qq.com').hostname;
				} catch {
					return '';
				}
			})();
			const isThirdParty = downloadHost && !downloadHost.endsWith('mail.qq.com') && !downloadHost.endsWith('qq.com');

			let category;
			if (dupKeys.has(dk)) category = DIR_DUP;
			else if (isThirdParty) category = DIR_MANUAL;
			else category = classifyExt(ext);

			const sender = a.sender?.addr || '';
			const dir = resolveSaveDir(category, { email: sender }, mailMap[a.mailid]);

			// Priority: (1) filename already has identity token → keep as-is;
			// (2) sender has compliant siblings → mirror their prefix; (3) synthesize from identity map.
			let filename;
			if (hasConventionDigits(origName)) {
				filename = (origName || 'unnamed') + '.' + ext;
			} else if (senderPrefix.has(sender)) {
				filename = senderPrefix.get(sender) + (origName || 'unnamed') + '.' + ext;
			} else {
				const segs = buildIdentitySegs(getIdentity(sender));
				if (origName) segs.push(origName);
				filename = (segs.length ? segs.join('_') : 'unnamed') + '.' + ext;
			}
			filename = sanitizeFilename(filename);

			const url = ensureAbsoluteUrl(a.download_url || '');

			const fileIndex = (perMailIdx.get(a.mailid) || 0) + 1;
			perMailIdx.set(a.mailid, fileIndex);

			const task = {
				id: id++,
				folderId,
				url,
				category,
				dir,
				filename,
				mailid: a.mailid,
				fileid: a.fileid,
				fileIndex,
				email: sender,
				quanpin: getQuanpin(sender),
				origName: a.name || '',
				status: 'pending',
			};
			const gk = dupGroupMap.get(dk);
			if (gk) task.dupGroup = gk;

			downloads.push(task);
		}

		// 互链：保留方挂出被替代清单，每个重复方挂回保留方引用。
		// manifest 序列化时只取需要的字段（见 buildManifestVal）。
		const taskByDk = new Map();
		for (const t of downloads) taskByDk.set(`${t.mailid}_${t.fileid}`, t);
		for (const [, info] of dupGroupInfo) {
			const keptTask = taskByDk.get(`${info.kept.eid}_${info.kept.fid}`);
			if (!keptTask) continue;
			const dupTasks = info.dups.map(d => taskByDk.get(`${d.eid}_${d.fid}`)).filter(Boolean);
			keptTask.dupCount = dupTasks.length;
			keptTask.dupReplaced = dupTasks.map(t => ({
				key: buildManifestKey(t),
				dir: t.dir,
				filename: t.filename,
				mailid: t.mailid,
				fileid: t.fileid,
			}));
			for (const dt of dupTasks) dt.keptTask = keptTask;
		}

		// Two-fold dedup: (1) Windows + macOS default FS are case-insensitive, so
		// "Photo.jpg" and "photo.jpg" race for the same slot — fold to lowercase.
		// (2) A counter that ignores the renamed name lets a real attachment
		// already called "file (2).jpg" collide with the rename of a duplicate
		// "file.jpg". Track every assigned name in a Set and probe forward.
		const taken = new Set();
		const dirKey = (n, d) => `${d}/${n}`.toLowerCase();
		for (const task of downloads) {
			if (!taken.has(dirKey(task.filename, task.dir))) {
				taken.add(dirKey(task.filename, task.dir));
				continue;
			}
			const dot = task.filename.lastIndexOf('.');
			const stem = dot > 0 ? task.filename.slice(0, dot) : task.filename;
			const ext = dot > 0 ? task.filename.slice(dot) : '';
			let n = 2;
			let cand;
			do {
				cand = `${stem} (${n++})${ext}`;
			} while (taken.has(dirKey(cand, task.dir)));
			task.filename = cand;
			taken.add(dirKey(cand, task.dir));
		}

		return downloads;
	}

	// ============================================================
	//  Manifest (local file tracking)
	// ============================================================

	async function readManifest() {
		try {
			const fh = await rootHandle.getFileHandle('manifest.json', { create: false });
			const file = await fh.getFile();
			const text = await file.text();
			return JSON.parse(text);
		} catch (e) {
			return {};
		}
	}

	async function writeManifest(manifest) {
		const fh = await rootHandle.getFileHandle('manifest.json', { create: true });
		const w = await fh.createWritable();
		await w.write(JSON.stringify(manifest, null, 2));
		await w.close();
	}

	let manifestCache = null;
	let manifestDirty = false;
	let manifestFlushTimer = null;

	function buildManifestVal(task, size) {
		const mailInfo = mailMap[task.mailid] || {};
		const val = {
			emailid: task.mailid,
			fileid: task.fileid,
			file_index: task.fileIndex,
			email: task.email,
			dir: task.dir,
			filename: task.filename,
			size,
			time: Date.now(),
		};
		if (task.origName && task.origName !== task.filename) val.orig_name = task.origName;
		if (mailInfo.subject) val.mail_subject = mailInfo.subject;
		if (mailInfo.senderNick) val.sender_name = mailInfo.senderNick;
		if (mailInfo.totime) val.mail_time = mailInfo.totime;
		if (task.dupGroup) val.dup_group = task.dupGroup;
		const kept = task.keptTask;
		if (kept) {
			// 重复方：记录“获胜者”落位，便于不再重跑管线就能从 `重复/` 反查关联。
			val.dup_role = 'duplicate';
			val.kept_by = `${kept.mailid}_${kept.fileid}`;
			val.kept_by_key = buildManifestKey(kept);
			val.kept_filename = kept.filename;
			val.kept_dir = kept.dir;
		} else if (task.dupGroup) {
			val.dup_role = 'kept';
			if (typeof task.dupCount === 'number') val.dup_count = task.dupCount;
			if (Array.isArray(task.dupReplaced) && task.dupReplaced.length) val.dup_replaced = task.dupReplaced;
		}
		return val;
	}

	// Debounce: coalesce bursts of appends from parallel workers into at most one write per 2s.
	async function manifestAppend(task, size) {
		if (!manifestCache) manifestCache = await readManifest();
		manifestCache[buildManifestKey(task)] = buildManifestVal(task, size);
		manifestDirty = true;

		if (!manifestFlushTimer) {
			manifestFlushTimer = setTimeout(() => {
				manifestFlushTimer = null;
				if (manifestDirty) {
					manifestDirty = false;
					writeManifest(manifestCache).catch(() => {});
				}
			}, 2000);
		}
	}

	async function manifestFlush() {
		if (manifestDirty && manifestCache) {
			manifestDirty = false;
			if (manifestFlushTimer) {
				clearTimeout(manifestFlushTimer);
				manifestFlushTimer = null;
			}
			await writeManifest(manifestCache);
		}
	}

	// Drop a `重复/_DUPLICATE_INDEX.md` next to the duplicate files themselves so anyone
	// browsing the folder can see which kept-side file each duplicate corresponds to —
	// without leaving the directory to consult manifest.json or report.md.
	async function writeDuplicateIndex(tasks) {
		const dups = tasks.filter(t => (t.category || t.dir) === DIR_DUP && t.dupGroup);
		if (dups.length === 0) return;
		const groups = new Map();
		for (const t of tasks) {
			if (!t.dupGroup) continue;
			if (!groups.has(t.dupGroup)) groups.set(t.dupGroup, []);
			groups.get(t.dupGroup).push(t);
		}
		const lines = [];
		lines.push(`# 重复投稿索引`);
		lines.push(``);
		lines.push(`> 共 ${groups.size} 组重复，${dups.length} 个被替代的附件。`);
		lines.push(`> 判定规则：sender_email + file_size 相同 → 按邮件时间保留最新。`);
		lines.push(``);
		let gi = 0;
		for (const [, group] of groups) {
			group.sort((a, b) => {
				const aCat = a.category || a.dir;
				const bCat = b.category || b.dir;
				if (aCat !== DIR_DUP && bCat === DIR_DUP) return -1;
				if (aCat === DIR_DUP && bCat !== DIR_DUP) return 1;
				const ta = mailMap[a.mailid]?.totime || 0;
				const tb = mailMap[b.mailid]?.totime || 0;
				return tb - ta;
			});
			gi++;
			lines.push(`## 组 ${gi}`);
			lines.push(``);
			lines.push(`| 角色 | 路径 | 发件人 | 邮箱 | 主题 | 邮件时间 |`);
			lines.push(`|------|------|--------|------|------|----------|`);
			for (const t of group) {
				const info = mailMap[t.mailid] || {};
				const role = (t.category || t.dir) !== DIR_DUP ? '● 保留' : '○ 重复';
				const path = `${t.dir}/${t.filename}`;
				lines.push(`| ${role} | ${escapeMd(path)} | ${escapeMd(info.senderNick)} | ${escapeMd(info.senderEmail)} | ${escapeMd(truncate(info.subject, 30))} | ${fmtDatetime(info.totime)} |`);
			}
			lines.push(``);
		}
		try {
			// _DUPLICATE_INDEX.md 始终放在 重复/ 顶层，便于人工审核（即便内部还按 bucket 分子目录）。
			const dh = await rootHandle.getDirectoryHandle(DIR_DUP, { create: true });
			const fh = await dh.getFileHandle('_DUPLICATE_INDEX.md', { create: true });
			const w = await fh.createWritable();
			await w.write(lines.join('\n'));
			await w.close();
		} catch (e) {
			console.error('[QQMail DL] Failed to write duplicate index:', e);
		}
	}

	// ============================================================
	//  Phase 8: Audit report
	// ============================================================

	// 缺省 detailTitle → 报告里有专属段落（DUP / MANUAL），而非普通清单。
	const DIR_META = [
		{ name: DIR_IMAGE, desc: 'jpg/png/webp/heic/ 等', detailTitle: '图片清单' },
		{ name: DIR_INLINE, desc: '正文嵌入图片', detailTitle: '内嵌图片清单' },
		{ name: DIR_PROJECT, desc: 'psd/ai/sketch/xd 等', detailTitle: '项目文件清单' },
		{ name: DIR_DOC, desc: 'pdf/doc/xls/ppt 等', detailTitle: '文档清单' },
		{ name: DIR_AUDIO, desc: 'mp3/wav/flac 等', detailTitle: '音频清单' },
		{ name: DIR_VIDEO, desc: 'mp4/mov/avi 等', detailTitle: '视频清单' },
		{ name: DIR_ARCHIVE, desc: 'zip/rar/7z 等', detailTitle: '压缩文件清单' },
		{ name: DIR_DUP, desc: '已保留最新' },
		{ name: DIR_OTHER, desc: '未归类格式', detailTitle: '其他文件清单' },
		{ name: DIR_MANUAL, desc: '第三方链接' },
	];

	function countByDir(tasks) {
		const s = {};
		for (const t of tasks) {
			const cat = t.category || t.dir;
			s[cat] = (s[cat] || 0) + 1;
		}
		return s;
	}

	function formatDirStats(stats) {
		return DIR_META.map(({ name }) => (name === DIR_IMAGE ? `${name} ${stats[name] || 0}` : stats[name] ? `${name} ${stats[name]}` : '')).filter(Boolean);
	}

	async function generateReport(tasks, pipelineStats) {
		const now = fmtDatetime(Date.now() / 1000);
		const done = tasks.filter(t => t.status === 'done');
		const failed = tasks.filter(t => t.status === 'failed');

		const byDir = {};
		for (const t of tasks) {
			const cat = t.category || t.dir;
			byDir[cat] = byDir[cat] || [];
			byDir[cat].push(t);
		}

		const lines = [];
		lines.push(`# ${folderName} · 投稿收集报告`);
		lines.push(``);
		lines.push(`> ${now} · ${done.length} 个文件 · ${failed.length > 0 ? failed.length + ' 失败' : '全部成功'}`);
		lines.push(``);

		lines.push(`## 概览`);
		lines.push(``);
		lines.push(`| 分类 | 数量 | 说明 |`);
		lines.push(`|------|------|------|`);
		for (const { name, desc } of DIR_META) {
			lines.push(`| ${name} | ${(byDir[name] || []).length} | ${desc} |`);
		}
		if (pipelineStats) {
			lines.push(`| 已撤回 | ${pipelineStats.recalledCount || 0} | 发信方已撤回 |`);
			lines.push(`| 空邮件 | ${pipelineStats.emptyCount || 0} | 无附件无内嵌图 |`);
			lines.push(`| 内嵌图 | ${pipelineStats.inlineCount || 0} | 从正文提取 |`);
		}
		lines.push(`| **合计** | **${tasks.length}** | 下载成功 ${done.length}，失败 ${failed.length} |`);
		lines.push(``);

		const totalMailsInTasks = new Set(tasks.map(t => t.mailid)).size;
		const totalScanned = pipelineStats?.totalScanned || totalMailsInTasks;
		const noAttachCount = Math.max(0, totalScanned - totalMailsInTasks - (pipelineStats?.recalledCount || 0));
		const manifest = manifestCache || (await readManifest());
		const manifestCount = Object.keys(manifest).length;
		const diskMatch = manifestCount >= done.length;

		lines.push(`## 审计校验`);
		lines.push(``);
		lines.push(`| 校验项 | 结果 |`);
		lines.push(`|--------|------|`);
		lines.push(`| 邮件 | 共 ${totalScanned} 封，${totalMailsInTasks} 封有附件，${noAttachCount} 封无附件 |`);
		lines.push(`| 附件 | 共 ${tasks.length} 个任务，成功 ${done.length}，失败 ${failed.length} |`);
		lines.push(`| 落盘 | manifest ${manifestCount} 条记录 ${diskMatch ? '✓' : '⚠ 不一致'} |`);
		lines.push(``);

		const aiItems = pipelineStats?.aiEnhancedItems || [];
		if (aiItems.length > 0) {
			lines.push(`## AI 主题解析`);
			lines.push(``);
			lines.push(`> 用 Chrome 内置 LanguageModel 从邮件主题里提取投稿信息，仅对发件人姓名缺失的邮件触发。`);
			lines.push(``);
			lines.push(`| # | 发件人 | 主题 | 姓名 | QQ | 手机 | 作品 |`);
			lines.push(`|---|--------|------|------|----|------|------|`);
			aiItems.forEach((it, i) => {
				const sender = escapeMd(it.nick || it.email);
				const subject = escapeMd(truncate(it.subject || '', 36));
				lines.push(`| ${i + 1} | ${sender} | ${subject} | ${escapeMd(it.parsed.name || '')} | ${escapeMd(it.parsed.qq || '')} | ${escapeMd(it.parsed.phone || '')} | ${escapeMd(truncate(it.parsed.work || '', 24))} |`);
			});
			lines.push(``);
		}

		// DIRs without `detailTitle` (DUP, MANUAL) get their own custom sections below.
		for (const { name, detailTitle } of DIR_META) {
			if (!detailTitle) continue;
			const items = byDir[name] || [];
			if (items.length === 0) continue;
			lines.push(`## ${detailTitle}`);
			lines.push(``);
			lines.push(`| # | 发件人 | 主题 | 最终文件名 |`);
			lines.push(`|---|--------|------|------------|`);
			items.forEach((t, i) => {
				const info = mailMap[t.mailid];
				lines.push(`| ${i + 1} | ${escapeMd(info?.senderEmail)} | ${escapeMd(truncate(info?.subject, 30))} | ${escapeMd(t.filename)} |`);
			});
			lines.push(``);
		}

		const dups = byDir[DIR_DUP] || [];
		if (dups.length > 0) {
			lines.push(`## 重复投稿`);
			lines.push(``);

			const dupGroups = new Map();
			for (const t of tasks) {
				if (!t.dupGroup) continue;
				if (!dupGroups.has(t.dupGroup)) dupGroups.set(t.dupGroup, []);
				dupGroups.get(t.dupGroup).push(t);
			}

			let groupIdx = 0;
			for (const [, group] of dupGroups) {
				group.sort((a, b) => {
					const aCat = a.category || a.dir;
					const bCat = b.category || b.dir;
					if (aCat !== DIR_DUP && bCat === DIR_DUP) return -1;
					if (aCat === DIR_DUP && bCat !== DIR_DUP) return 1;
					const ta = mailMap[a.mailid]?.totime || 0;
					const tb = mailMap[b.mailid]?.totime || 0;
					return tb - ta;
				});
				groupIdx++;
				lines.push(`### 重复组 ${groupIdx}`);
				lines.push(``);
				lines.push(`| 状态 | 路径 | 发件人 | 邮箱 | 主题 | 时间 |`);
				lines.push(`|------|------|--------|------|------|------|`);
				for (const t of group) {
					const info = mailMap[t.mailid] || {};
					const kept = (t.category || t.dir) !== DIR_DUP ? '● 保留' : '○ 重复';
					const subject = truncate(info.subject, 25);
					const path = `${t.dir}/${t.filename}`;
					lines.push(`| ${kept} | ${escapeMd(path)} | ${escapeMd(info.senderNick)} | ${escapeMd(info.senderEmail)} | ${escapeMd(subject)} | ${fmtDatetime(info.totime)} |`);
				}
				lines.push(``);
			}
		}

		const manual = byDir[DIR_MANUAL] || [];
		if (manual.length > 0) {
			lines.push(`## 待人工处理`);
			lines.push(``);
			lines.push(`| 文件名 | 发件人 | URL |`);
			lines.push(`|--------|--------|-----|`);
			for (const t of manual) {
				const info = mailMap[t.mailid];
				lines.push(`| ${escapeMd(t.filename)} | ${escapeMd(info?.senderEmail)} | ${escapeMd(t.url.slice(0, 60))}... |`);
			}
			lines.push(``);
		}

		if (failed.length > 0) {
			lines.push(`## 下载失败`);
			lines.push(``);
			lines.push(`| 文件名 | 错误 |`);
			lines.push(`|--------|------|`);
			for (const t of failed) {
				lines.push(`| ${escapeMd(t.filename)} | ${escapeMd(t.error || 'unknown')} |`);
			}
			lines.push(``);
		}

		const content = lines.join('\n');

		try {
			const fh = await rootHandle.getFileHandle('report.md', { create: true });
			const w = await fh.createWritable();
			await w.write(content);
			await w.close();
		} catch (e) {
			console.error('[QQMail DL] Failed to write report:', e);
		}

		return { done: done.length, failed: failed.length, total: tasks.length, manifestCount };
	}

	// ============================================================
	//  Download engine (with session expiry recovery)
	// ============================================================

	let sessionExpired = false;
	let sessionRecoverResolve = null;

	function waitForSessionRecovery() {
		sessionExpired = true;
		return new Promise(resolve => {
			sessionRecoverResolve = resolve;
			showSessionExpiredUI();
		});
	}

	function showSessionExpiredUI() {
		const panel = getOrCreatePanel();
		const banner = document.createElement('div');
		banner.id = '__dl_session_banner';
		banner.style.cssText = 'background:#FFF3E0;border:1px solid #FFB74D;border-radius:6px;padding:10px 16px;margin-bottom:10px;display:flex;align-items:center;gap:8px;';
		banner.innerHTML = `
      <span style="color:#E65100;font-weight:700;">⚠ 登录态失效</span>
      <span style="color:#BF360C;font-size:13px;">请刷新页面重新登录，然后回到此文件夹</span>
      <span style="flex:1;"></span>
      <button id="__dl_recover" style="background:#0F7AF5;color:#fff;border:none;border-radius:6px;padding:4px 12px;font-size:13px;cursor:pointer;">已刷新，继续下载</button>
    `;

		const existing = document.getElementById('__dl_session_banner');
		if (existing) existing.remove();
		banner.querySelector('#__dl_recover').addEventListener('click', async () => {
			const newSid = getSidFromUrl();
			if (!newSid) {
				banner.querySelector('span:nth-child(2)').textContent = 'URL 中未找到 sid，请确认已刷新并进入文件夹';
				return;
			}
			const oldSid = sid;
			sid = newSid;
			const check = await verifySession();
			if (!check) {
				sid = oldSid;
				banner.querySelector('span:nth-child(2)').textContent = '新 session 无效，请重新登录';
				return;
			}
			banner.remove();
			sessionExpired = false;
			sessionRecoverResolve?.(newSid);
			sessionRecoverResolve = null;
		});
		panel.insertBefore(banner, panel.firstChild);
	}

	// Also auto-detect: listen for URL changes that bring a new sid
	let sidRecoveryInterval = null;
	function setupAutoSidRecovery() {
		if (sidRecoveryInterval) clearInterval(sidRecoveryInterval);
		sidRecoveryInterval = setInterval(() => {
			if (!sessionExpired) return;
			const newSid = getSidFromUrl();
			if (newSid && newSid !== sid) {
				const recoverBtn = document.getElementById('__dl_recover');
				if (recoverBtn) recoverBtn.click();
			}
		}, 2000);
	}

	async function startEngine(tasks, onProgress) {
		if (engineRunning) return;
		engineRunning = true;

		const dirCache = new Map();
		async function getDirHandle(relPath) {
			const cached = dirCache.get(relPath);
			if (cached) return cached;
			const handle = await resolveDirHandle(rootHandle, relPath, { create: true });
			dirCache.set(relPath, handle);
			return handle;
		}

		async function downloadOne(task) {
			try {
				const blob = await new Promise((res, rej) => {
					const xhr = new XMLHttpRequest();
					xhr.open('GET', task.url, true);
					xhr.responseType = 'blob';
					xhr.onload = () => (xhr.status === 200 ? res(xhr.response) : rej(new Error(`HTTP ${xhr.status}`)));
					xhr.onerror = () => rej(new Error('network'));
					xhr.send();
				});

				// QQ Mail returns a JSON error body (not HTTP 4xx) when the session expires.
				if (blob.type === 'application/json' && blob.size < 1000) {
					const j = JSON.parse(await blob.text());
					if (j.head?.ret === -20002 || j.ret === -20002) throw new Error('session_expired');
					if (j.head?.ret !== undefined) throw new Error('api_error');
				}

				const dh = await getDirHandle(task.dir);
				const fh = await dh.getFileHandle(task.filename, { create: true });
				const w = await fh.createWritable();
				await w.write(blob);
				await w.close();
				task.status = 'done';
				await manifestAppend(task, blob.size);
			} catch (e) {
				if (e.message === 'session_expired') throw e; // bubble up for retry; caller requeues
				task.status = 'failed';
				task.error = e.message;
			}
			if (task.status !== 'pending') await dbPut('tasks', task);
		}

		const mailTotalCount = new Map();
		const mailDoneCount = new Map();
		for (const task of tasks) {
			mailTotalCount.set(task.mailid, (mailTotalCount.get(task.mailid) || 0) + 1);
			mailDoneCount.set(task.mailid, 0);
		}

		const wrappedProgress = task => {
			onProgress?.(task);
			if (task.status === 'done' && task.mailid) {
				const mid = task.mailid;
				mailDoneCount.set(mid, (mailDoneCount.get(mid) || 0) + 1);
				if (mailDoneCount.get(mid) >= mailTotalCount.get(mid)) {
					markMailRead(mid).catch(() => {});
				}
			}
		};

		const queue = [...tasks];
		const workers = [];
		for (let i = 0; i < CONCURRENCY; i++) {
			workers.push(
				(async () => {
					while (queue.length > 0 && engineRunning) {
						const task = queue.shift();
						try {
							await downloadOne(task);
							wrappedProgress(task);
						} catch (e) {
							if (e.message === 'session_expired') {
								queue.unshift(task);
								// Exactly one worker drives recovery; the rest poll until sessionExpired clears.
								if (!sessionExpired) {
									const newSid = await waitForSessionRecovery();
									for (const t of queue) {
										t.url = replaceSid(t.url, newSid);
									}
								} else {
									await new Promise(r => {
										const iv = setInterval(() => {
											if (!sessionExpired) {
												clearInterval(iv);
												r();
											}
										}, 500);
									});
								}
								continue;
							}
						}
					}
				})()
			);
		}
		await Promise.all(workers);
		await manifestFlush();
		engineRunning = false;
	}

	// ============================================================
	//  UI
	// ============================================================

	const ICONS = {
		download:
			'<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" style="color:#0F7AF5;flex-shrink:0;"><path d="M8 1a.75.75 0 0 1 .75.75v7.19l2.22-2.22a.75.75 0 1 1 1.06 1.06l-3.5 3.5a.75.75 0 0 1-1.06 0l-3.5-3.5a.75.75 0 1 1 1.06-1.06l2.22 2.22V1.75A.75.75 0 0 1 8 1ZM2.75 13a.75.75 0 0 0 0 1.5h10.5a.75.75 0 0 0 0-1.5H2.75Z"/></svg>',
		check: '<svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" fill="#07C160" style="flex-shrink:0;"><path d="M12.03 4.47a.75.75 0 0 1 0 1.06l-5.5 5.5a.75.75 0 0 1-1.06 0l-2.5-2.5a.75.75 0 1 1 1.06-1.06L6 9.44l4.97-4.97a.75.75 0 0 1 1.06 0Z"/></svg>',
		fail: '<svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" fill="#E84C3D" style="flex-shrink:0;"><path d="M4.47 3.47a.75.75 0 0 0-1.06 1.06L6.44 7.5 3.41 10.53a.75.75 0 1 0 1.06 1.06L7.5 8.56l3.03 3.03a.75.75 0 0 0 1.06-1.06L8.56 7.5l3.03-3.03a.75.75 0 0 0-1.06-1.06L7.5 6.44 4.47 3.47Z"/></svg>',
		mail: '<svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" fill="rgba(20,46,77,0.4)" style="flex-shrink:0;"><path fill-rule="evenodd" d="M2 3a1 1 0 0 0-1 1v6a1 1 0 0 0 1 1h8a1 1 0 0 0 1-1V4a1 1 0 0 0-1-1H2Zm.22 1.97a.75.75 0 0 0-.44 1.36l3.5 2.5a1.25 1.25 0 0 0 1.44 0l3.5-2.5a.75.75 0 0 0-.44-1.36L6.5 7.22a.75.75 0 0 1-.86 0L2.22 4.97Z"/></svg>',
		file: '<svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" fill="none" style="flex-shrink:0;"><rect x="1" y="1" width="10" height="10" rx="2" stroke="rgba(20,46,77,0.2)" stroke-width="1"/></svg>',
	};

	const CARD_STYLE = `
    background: #fff;
    font-family: -apple-system, BlinkMacSystemFont, system-ui, "PingFang SC", "Microsoft YaHei UI", "Microsoft YaHei", sans-serif;
    font-size: 13px;
    color: #1a2033;
    line-height: 1.6;
    padding: 16px 20px;
    border-bottom: 1px solid rgba(20,46,77,0.06);
  `.replace(/\n\s+/g, '');

	const BTN_PRIMARY_STYLE = 'background:#0F7AF5;color:#fff;border:none;border-radius:6px;padding:6px 16px;font-size:14px;cursor:pointer;font-family:inherit;';
	const TEXT_MUTED = 'font-size:14px;color:rgba(20,46,77,0.45);';

	// `subtitleId` is set only for UIs whose subtitle is live-updated by updateScanMessage().
	function headerRow(subtitle, right = '', subtitleId = '') {
		const idAttr = subtitleId ? ` id="${subtitleId}"` : '';
		return `<div style="display:flex;align-items:center;gap:8px;height:32px;">
			<span style="font-size:16px;font-weight:700;color:rgb(19,24,29);">附件下载</span>
			<span${idAttr} style="${TEXT_MUTED}">${subtitle}</span>
			<span style="flex:1;"></span>${right}
		</div>`;
	}

	// AI 解析结果折叠块。每条记录展示发件人 + 主题片段 + 提取到的字段，回答
	// "AI 到底解析了什么"——空字段不渲染，避免噪声。
	function renderAIEnhanceDetails(items) {
		if (!items || items.length === 0) return '';
		const fmtField = (label, val) => (val ? `<span style="display:inline-block;margin-right:10px;"><span style="color:rgba(20,46,77,0.45);">${label}</span>${escapeHtml(val)}</span>` : '');
		const sourceLabel = src => (src === 'search' ? '搜索' : src === 'search+ai' ? '搜索+AI' : 'AI');
		const rows = items
			.map(it => {
				const fields = [fmtField('姓名 ', it.parsed.name), fmtField('QQ ', it.parsed.qq), fmtField('手机 ', it.parsed.phone), fmtField('作品 ', it.parsed.work && truncate(it.parsed.work, 18))].filter(Boolean).join('');
				const sender = escapeHtml(it.nick || it.email.split('@')[0]);
				const subject = escapeHtml(truncate(it.subject || '', 36));
				const tag = `<span style="display:inline-block;padding:0 4px;margin-right:6px;background:rgba(20,46,77,0.08);border-radius:3px;font-size:11px;color:rgba(20,46,77,0.6);">${sourceLabel(it.source)}</span>`;
				return `<div style="padding:6px 0;border-top:1px solid rgba(20,46,77,0.06);">
				<div style="font-size:12px;color:rgba(20,46,77,0.5);">${tag}${sender} · ${subject}</div>
				<div style="font-size:12px;color:rgba(20,46,77,0.75);margin-top:2px;">${fields || '<span style="color:rgba(20,46,77,0.35);">未提取到字段</span>'}</div>
			</div>`;
			})
			.join('');
		return `<details style="margin-top:8px;font-size:13px;">
			<summary style="cursor:pointer;color:rgba(20,46,77,0.55);user-select:none;">身份补全 ${items.length} 条记录（点开查看详情）</summary>
			<div style="margin:4px 0 0;">${rows}</div>
		</details>`;
	}

	function getOrCreatePanel() {
		let panel = document.getElementById('__dl_panel');
		if (!panel) {
			panel = document.createElement('div');
			panel.id = '__dl_panel';
			panel.style.cssText = CARD_STYLE;
		}
		return panel;
	}

	async function mountPanel(panel) {
		if (panel.parentElement) return;
		const mailApp = await waitForSelector('.mail_app');
		if (mailApp?.firstChild) mailApp.insertBefore(panel, mailApp.firstChild);
	}

	function showStartUI() {
		const panel = getOrCreatePanel();
		panel.innerHTML = headerRow('点击开始扫描当前文件夹', `<button id="__dl_start" style="${BTN_PRIMARY_STYLE}">开始扫描</button>`);
		panel.querySelector('#__dl_start').onclick = () => runFullPipeline();
		mountPanel(panel);
	}

	function showResumeUI(pendingCount) {
		const panel = getOrCreatePanel();
		panel.innerHTML = headerRow(
			`还有 <strong style="color:rgb(19,24,29);">${pendingCount}</strong> 个待下载`,
			`<button id="__dl_resume" style="${BTN_PRIMARY_STYLE}">选择目录</button>
			 <button id="__dl_reset" style="background:none;color:rgba(20,46,77,0.45);border:1px solid rgba(20,46,77,0.1);border-radius:6px;padding:6px 12px;font-size:13px;cursor:pointer;font-family:inherit;">重新扫描</button>`
		);
		panel.querySelector('#__dl_resume').onclick = async () => {
			try {
				rootHandle = await window.showDirectoryPicker({ mode: 'readwrite' });
				await resumeDownloads();
			} catch (e) {}
		};
		panel.querySelector('#__dl_reset').onclick = async () => {
			await dbDeleteByFolder(folderId);
			runFullPipeline();
		};
		mountPanel(panel);
	}

	function showProgressUI(done, total, failed, mailCount) {
		const panel = getOrCreatePanel();
		const pct = total > 0 ? (((done + failed) / total) * 100).toFixed(1) : '0';
		const mailLabel = mailCount ? `${mailCount} 封邮件` : '';
		const right = `
			<span id="__dl_speed_inline" style="font-size:13px;color:rgba(20,46,77,0.45);"></span>
			<span style="font-size:13px;color:rgba(20,46,77,0.45);"><span id="__dl_done">${done}</span>/${total} 个附件</span>
			<span id="__dl_pct" style="font-size:13px;color:rgba(20,46,77,0.45);">${pct}%</span>`;
		panel.innerHTML = `
			${headerRow(mailLabel, right)}
			<div style="background:rgba(20,46,77,0.06);border-radius:100px;height:4px;margin:10px 0 12px;">
				<div id="__dl_bar" style="background:#0F7AF5;height:100%;border-radius:100px;width:${pct}%;transition:width 0.3s;"></div>
			</div>
			<div id="__dl_fail_section"></div>
			<div id="__dl_current_mail" style="font-size:13px;"></div>
			<div id="__dl_current" style="margin-top:4px;font-size:13px;"></div>
		`;
		mountPanel(panel);
	}

	// total / baseDone / baseFailed all use the OUTER scope — i.e. all attachments in
	// this folder, including those already downloaded. The tracker increments from the
	// base counts so the panel stays in sync with showProgressUI's initial render even
	// when the engine only processes a partial pending slice.
	function createProgressTracker(total, baseDone = 0, baseFailed = 0) {
		let done = baseDone;
		let failed = baseFailed;
		const startTime = Date.now();
		const failedTasks = [];
		const recentTasks = [];

		const bar = document.getElementById('__dl_bar');
		const pctEl = document.getElementById('__dl_pct');
		const doneEl = document.getElementById('__dl_done');
		const speedEl = document.getElementById('__dl_speed_inline');
		const mailDiv = document.getElementById('__dl_current_mail');
		const filesDiv = document.getElementById('__dl_current');
		const failSection = document.getElementById('__dl_fail_section');

		let lastMailId = null;
		let lastFailCount = 0;

		function renderMailInfo(mInfo) {
			const idx = mInfo.mailIdx || '';
			const count = mInfo.attachCount || 0;
			const email = escapeHtml(mInfo.senderEmail || '');
			const nick = escapeHtml(mInfo.senderNick || '');
			const subject = escapeHtml(mInfo.subject || '');
			mailDiv.innerHTML = `
				<div style="display:flex;align-items:center;gap:8px;color:rgba(20,46,77,0.55);margin-bottom:2px;">
					${ICONS.mail}
					<span style="color:rgba(20,46,77,0.35);white-space:nowrap;">${idx}</span>
					<span style="flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;">${subject}</span>
					<span style="color:rgba(20,46,77,0.35);white-space:nowrap;">${email}</span>
					<span style="white-space:nowrap;">${nick}</span>
					<span style="color:rgba(20,46,77,0.35);white-space:nowrap;">+${count}</span>
				</div>`;
		}

		function renderRecentFiles() {
			filesDiv.innerHTML = recentTasks
				.slice(-3)
				.map(t => {
					const ai = mailMap[t.mailid + '|' + t.fileid];
					const name = escapeHtml(ai?.origName || t.filename);
					const idx = ai?.attachIdx || '';
					const tot = ai?.attachTotal || '';
					return `<div style="display:flex;align-items:center;gap:6px;margin-bottom:2px;line-height:1.6;color:rgba(20,46,77,0.55);">
						${ICONS.file}
						<span style="color:rgba(20,46,77,0.35);font-size:11px;white-space:nowrap;">${idx}/${tot}</span>
						<span style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap;">${name}</span>
					</div>`;
				})
				.join('');
		}

		function renderFailSection() {
			failSection.innerHTML = `
				<div style="margin-bottom:8px;padding-bottom:8px;border-bottom:1px solid rgba(20,46,77,0.06);">
					<div style="display:flex;align-items:center;gap:6px;margin-bottom:6px;">
						${ICONS.fail}
						<span style="color:#E84C3D;font-weight:700;font-size:14px;">失败 ${failedTasks.length}</span>
						<span style="flex:1;"></span>
						<button id="__dl_retry_all" style="background:#0F7AF5;color:#fff;border:none;border-radius:4px;padding:2px 10px;font-size:11px;cursor:pointer;">重试全部</button>
					</div>
					${failedTasks
						.slice(-3)
						.map(t => `<div style="font-size:12px;color:rgba(20,46,77,0.55);margin-bottom:2px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;">${escapeHtml(t.filename)}</div>`)
						.join('')}
				</div>`;
			const retryBtn = document.getElementById('__dl_retry_all');
			if (retryBtn) retryBtn.onclick = () => retryFailed(failedTasks);
		}

		return {
			onTask(task) {
				if (task.status === 'done') done++;
				else if (task.status === 'failed') {
					failed++;
					failedTasks.push(task);
				}
				recentTasks.push(task);
				if (recentTasks.length > 5) recentTasks.shift();

				const pct = (((done + failed) / total) * 100).toFixed(1);
				const el = (Date.now() - startTime) / 1000;
				// Speed/ETA are session-relative — only this run's progress, not the
				// already-downloaded base. Otherwise speed inflates wildly on resume.
				const sessionDone = done - baseDone;
				const sessionFailed = failed - baseFailed;
				const speed = el > 0 ? (sessionDone + sessionFailed) / el : 0;
				const rem = total - done - failed;
				const eta = speed > 0 ? Math.ceil(rem / speed) : 0;

				if (bar) bar.style.width = pct + '%';
				if (pctEl) pctEl.textContent = pct + '%';
				if (doneEl) doneEl.textContent = done;
				if (speedEl) {
					const etaMin = Math.floor(eta / 60);
					const etaSec = eta % 60;
					speedEl.textContent = done + failed >= total ? `已完成 · ${Math.floor(el)}秒` : `${speed.toFixed(1)}/秒 · ${etaMin > 0 ? etaMin + '分' : ''}${etaSec}秒`;
				}

				if (mailDiv && task.mailid !== lastMailId) {
					const mInfo = mailMap[task.mailid];
					if (mInfo) renderMailInfo(mInfo);
					lastMailId = task.mailid;
				}
				if (filesDiv) renderRecentFiles();

				if (failSection && failedTasks.length !== lastFailCount) {
					lastFailCount = failedTasks.length;
					if (failedTasks.length > 0) renderFailSection();
				}

				if (done + failed >= total && bar) {
					bar.style.background = failed > 0 ? '#E84C3D' : '#07C160';
				}
			},
		};
	}

	// ============================================================
	//  Scanning UI
	// ============================================================

	function showScanningUI(message) {
		const panel = getOrCreatePanel();
		panel.innerHTML = headerRow(message, '', '__dl_scan_msg');
		mountPanel(panel);
	}

	function updateScanMessage(msg) {
		const el = document.getElementById('__dl_scan_msg');
		if (el) el.textContent = msg;
	}

	// ============================================================
	//  Pipeline
	// ============================================================

	async function runFullPipeline() {
		sid = getSidFromUrl();
		folderId = getFolderIdFromUrl();

		if (!sid || !folderId) {
			showScanningUI('请先打开一个邮件文件夹');
			return;
		}
		try {
			await _runFullPipeline();
		} catch (e) {
			console.error('[QQMailDL] pipeline error:', e);
			showScanningUI(`出错: ${escapeHtml(e.message || String(e))}`);
		}
	}

	async function _runFullPipeline() {
		showScanningUI('验证登录状态...');
		const folderData = await verifySession();
		if (!folderData) {
			showScanningUI('登录态失效，请刷新页面重新登录');
			return;
		}

		// Kick off contact-book fetch in parallel — we need it before building the
		// download list (manifest keys embed quanpin), but it's slow enough that
		// running it alongside scanAllMails cuts overall startup latency.
		const addrPromise = fetchAddrList();

		const allFolders = [...(folderData.body.list.personal_list || []), ...(folderData.body.list.sys_list || [])];
		const folder = allFolders.find(f => f.dirid === folderId);
		folderName = folder?.name || `文件夹${folderId}`;
		const totalMailNum = folder?.total_num || 0;

		if (totalMailNum === 0) {
			showScanningUI(`${escapeHtml(folderName)} 中没有邮件`);
			return;
		}

		showScanningUI(`扫描邮件...`);
		const allMails = await scanAllMails(totalMailNum, (loaded, total) => {
			updateScanMessage(`扫描邮件 ${loaded}/${total}`);
		});

		const attachments = [];
		let mailTotal = 0;
		for (const mail of allMails) {
			const attaches = getAttachments(mail);
			if (attaches.length === 0) continue;
			mailTotal++;
			const email = getSenderEmail(mail);
			const nick = getSenderNick(mail);
			for (const a of attaches) {
				attachments.push({
					mailid: mail.emailid,
					fileid: a.fileid,
					name: a.name,
					size: a.size,
					type: a.type || '',
					download_url: a.download_url || '',
					ctime: mail.totime,
					subject: mail.subject,
					sender: { addr: email, name: nick },
				});
			}
		}

		// Build over allMails (not just attachments) so senders of inline-only mails
		// also enter identityMap and become eligible for AI subject parsing.
		buildIdentityMap(allMails);
		buildMailMapFromAttach(attachments);

		const markUnreadPromise = markAllUnread();

		// Identity enrichment runs invisibly: search starts immediately alongside
		// AI init, and stage 2 inside the search awaits aiReadyPromise — so the
		// user only sees the existing "AI 增强解析" step, never a separate "搜索" one.
		const aiReadyPromise = initBuiltinAI();
		const searchPromise = enrichIdentityFromSearch(allMails, aiReadyPromise);

		const [aiReady, searchResult] = await Promise.all([aiReadyPromise, searchPromise]);
		let aiEnhancedCount = searchResult.count;
		let aiEnhancedItems = [...searchResult.items];

		if (aiReady) {
			updateScanMessage('AI 增强解析...');
			const result = await enhanceIdentityWithAI(allMails, updateScanMessage);
			aiEnhancedCount += result.count;
			aiEnhancedItems.push(...result.items);
		}

		updateScanMessage(`检查撤回和空邮件...`);
		const { recalled } = await processRecalledMails(allMails, updateScanMessage);

		// quanpin/jianpin must be in place before any task or inline entry is built —
		// manifest keys reference them, and a half-populated addrMap would scatter the
		// same sender across two key namespaces (quanpin + email-fallback).
		addrMap = await addrPromise;

		const noAttachMails = allMails.filter(m => !hasAttachments(m) && !(m.subject || '').startsWith('发信方已撤回邮件：'));
		const sendersWithAttach = new Set(attachments.map(a => a.sender?.addr).filter(Boolean));

		let inlineEntries = [];
		let emptyMails = [];
		if (noAttachMails.length > 0) {
			updateScanMessage(`检查 ${noAttachMails.length} 封无附件邮件...`);
			const innerResult = await processInnerPicList(noAttachMails, sendersWithAttach, updateScanMessage);
			inlineEntries = innerResult.inlineEntries;
			emptyMails = innerResult.emptyMails;
		}

		await markUnreadPromise;

		const statParts = [
			`${totalMailNum} 封邮件`,
			`${attachments.length} 个附件（${mailTotal} 封有附件）`,
			recalled.length > 0 ? `${recalled.length} 封已撤回` : '',
			inlineEntries.length > 0 ? `${inlineEntries.length} 个正文图片` : '',
			emptyMails.length > 0 ? `${emptyMails.length} 封空邮件` : '',
		].filter(Boolean);

		const panel = getOrCreatePanel();
		panel.innerHTML = `
			${headerRow('扫描完成', `<button id="__dl_pick" style="${BTN_PRIMARY_STYLE}">选择保存目录</button>`)}
			<div style="display:flex;flex-wrap:wrap;gap:6px 16px;margin-top:8px;font-size:13px;color:rgba(20,46,77,0.55);">
				${statParts.map(s => `<span>${s}</span>`).join('')}
			</div>
			${renderAIEnhanceDetails(aiEnhancedItems)}
		`;
		const pickPromise = new Promise(resolve => {
			panel.querySelector('#__dl_pick').addEventListener('click', async () => {
				try {
					const handle = await window.showDirectoryPicker({ mode: 'readwrite' });
					resolve(handle);
				} catch (e) {}
			});
		});
		mountPanel(panel);
		rootHandle = await pickPromise;

		showScanningUI('分析分类...');
		const downloads = buildDownloadListFromAttach(attachments);

		for (const entry of inlineEntries) {
			entry.id = downloads.length;
			entry.status = 'pending';
			downloads.push(entry);
		}

		updateScanMessage('对比本地文件...');
		manifestCache = await readManifest();
		const manifestKeys = new Set(Object.keys(manifestCache));

		// Map<dirName, Map<filename, FileSystemFileHandle>> — keep handles so the manifest
		// rebuild below can read file size without re-walking the tree.
		const diskFileSet = new Map();
		const dirNames = new Set(downloads.map(d => d.dir));
		for (const dirName of dirNames) {
			const fileMap = new Map();
			try {
				const dh = await resolveDirHandle(rootHandle, dirName, { create: false });
				// Walk subfolders too when SCAN_SUBFOLDERS is on — users often archive
				// into 图片/2026-03/ etc. Match by bare filename so a moved file still
				// counts as already-downloaded.
				const stack = [dh];
				while (stack.length > 0) {
					const cur = stack.pop();
					for await (const [name, handle] of cur) {
						if (handle.kind === 'file') {
							if (!fileMap.has(name)) fileMap.set(name, handle);
						} else if (handle.kind === 'directory' && SCAN_SUBFOLDERS) {
							stack.push(handle);
						}
					}
				}
			} catch {}
			diskFileSet.set(dirName, fileMap);
		}

		let alreadyDownloaded = 0;
		let manifestRebuilt = false;
		for (const task of downloads) {
			const mKey = buildManifestKey(task);
			const fileMap = diskFileSet.get(task.dir);
			const fileHandle = fileMap?.get(task.filename);
			const onDisk = !!fileHandle;
			const inManifest = manifestKeys.has(mKey);

			if (onDisk) {
				task.status = 'done';
				alreadyDownloaded++;
				if (!inManifest) {
					try {
						const file = await fileHandle.getFile();
						manifestCache[mKey] = buildManifestVal(task, file.size);
						manifestRebuilt = true;
					} catch {}
				}
			} else if (inManifest) {
				delete manifestCache[mKey];
				manifestRebuilt = true;
			}
		}
		if (manifestRebuilt) await writeManifest(manifestCache);

		const diskTotal = [...diskFileSet.values()].reduce((s, m) => s + m.size, 0);
		console.log(`[QQMailDL] 本地对比: ${diskTotal} 磁盘文件, ${alreadyDownloaded} 匹配, ${downloads.length - alreadyDownloaded} 待下载`);

		const mailCount = mailTotal;
		const pipelineStats = {
			recalledCount: recalled.length,
			emptyCount: emptyMails.length,
			inlineCount: inlineEntries.length,
			totalScanned: totalMailNum,
			aiEnhancedCount,
			aiEnhancedItems,
			alreadyDownloaded,
		};

		const stats = countByDir(downloads);
		const renamedCount = downloads.filter(d => {
			const aInfo = mailMap[d.mailid + '|' + d.fileid];
			return aInfo && d.filename !== aInfo.origName;
		}).length;
		const pending = downloads.filter(t => t.status === 'pending');

		updateScanMessage('保存下载列表...');
		await dbDeleteByFolder(folderId);
		await dbPutBatch('tasks', downloads);

		const dlStatLine = [
			`${totalMailNum} 封邮件`,
			`${downloads.length} 个附件`,
			alreadyDownloaded > 0 ? `已下载 ${alreadyDownloaded}` : '',
			pending.length > 0 ? `待下载 ${pending.length}` : '',
			...formatDirStats(stats),
			recalled.length > 0 ? `已撤回 ${recalled.length}` : '',
			emptyMails.length > 0 ? `空邮件 ${emptyMails.length}` : '',
			inlineEntries.length > 0 ? `内嵌图 ${inlineEntries.length}` : '',
			renamedCount > 0 ? `重命名 ${renamedCount}` : '',
		]
			.filter(Boolean)
			.join(' · ');

		if (pending.length === 0) {
			await syncReadStatus(downloads);
			await onDownloadComplete(downloads, mailCount, pipelineStats);
			return;
		}

		if (alreadyDownloaded > 0) {
			updateScanMessage(`跳过 ${alreadyDownloaded} 个已有文件，同步已读状态...`);
			await syncReadStatus(downloads);
		}

		showProgressUI(alreadyDownloaded, downloads.length, 0, mailCount);
		const scanMsg = document.getElementById('__dl_scan_msg');
		if (scanMsg) scanMsg.textContent = dlStatLine;

		const tracker = createProgressTracker(downloads.length, alreadyDownloaded);
		await startEngine(pending, task => tracker.onTask(task));

		updateScanMessage('标记已下载...');
		const doneMails = [...new Set(downloads.filter(t => t.status === 'done').map(t => t.mailid))];
		await batchParallel(doneMails, 10, mid => addTag(mid, TAG_DOWNLOADED).catch(() => {}));

		await tagDuplicateMails(downloads, n => updateScanMessage(`标记重复 ${n} 封...`));
		await writeDuplicateIndex(downloads);

		await onDownloadComplete(downloads, mailCount, pipelineStats);
	}

	async function syncReadStatus(tasks) {
		const mailAttachCount = new Map();
		for (const task of tasks) {
			const mid = task.mailid;
			if (!mid) continue;
			if (!mailAttachCount.has(mid)) mailAttachCount.set(mid, { total: 0, done: 0 });
			const m = mailAttachCount.get(mid);
			m.total++;
			if (task.status === 'done') m.done++;
		}
		const readPromises = [];
		for (const [mid, counts] of mailAttachCount) {
			if (counts.done >= counts.total) {
				readPromises.push(markMailRead(mid).catch(() => {}));
			}
		}
		for (let i = 0; i < readPromises.length; i += 10) {
			await Promise.all(readPromises.slice(i, i + 10));
		}
	}

	async function onDownloadComplete(tasks, mc, pipelineStats) {
		showScanningUI('生成审计报告...');
		const reportStats = await generateReport(tasks, pipelineStats);

		const panel = getOrCreatePanel();
		const done = tasks.filter(t => t.status === 'done').length;
		const failed = tasks.filter(t => t.status === 'failed').length;
		const total = tasks.length;
		const stats = countByDir(tasks);

		const summaryParts = [`${done}/${total} 成功`, failed > 0 ? `${failed} 失败` : '', ...formatDirStats(stats)].filter(Boolean).join(' · ');

		const barColor = failed > 0 ? '#E84C3D' : '#07C160';

		panel.innerHTML = `
			<div style="display:flex;align-items:center;gap:8px;height:32px;">
				<span style="font-size:16px;font-weight:700;color:rgb(19,24,29);">附件下载</span>
				${ICONS.check}
				<span style="${TEXT_MUTED}">${summaryParts}</span>
				<span style="flex:1;"></span>
				<span style="font-size:12px;color:rgba(20,46,77,0.35);">report.md 已保存</span>
			</div>
			<div style="background:rgba(20,46,77,0.06);border-radius:100px;height:4px;margin:10px 0 0;">
				<div style="background:${barColor};height:100%;border-radius:100px;width:100%;"></div>
			</div>
		`;
		mountPanel(panel);
	}

	async function resumeDownloads() {
		const allStored = await dbGetAll('tasks');
		const allTasks = allStored.filter(t => t.folderId === folderId);
		const pending = allTasks.filter(t => t.status === 'pending' || t.status === 'failed');
		const total = allTasks.length;

		const currentSid = getSidFromUrl();
		if (currentSid) {
			for (const t of pending) {
				t.url = replaceSid(t.url, currentSid);
				t.status = 'pending';
				t.error = undefined;
			}
			await dbPutBatch('tasks', pending);
			sid = currentSid;
		}

		let mc = 0;
		if (Object.keys(mailMap).length === 0) {
			folderId = getFolderIdFromUrl();
			if (folderId && sid) {
				try {
					const folderData = await verifySession();
					if (folderData) {
						const allFolders = [...(folderData.body.list.personal_list || []), ...(folderData.body.list.sys_list || [])];
						const folder = allFolders.find(f => f.dirid === folderId);
						const totalNum = folder?.total_num || 0;
						if (totalNum > 0) {
							const allMails = await scanAllMails(totalNum);
							buildIdentityMap(allMails);
							buildMailMap(allMails);
							mc = allMails.filter(hasAttachments).length;
						}
					}
				} catch (e) {}
			}
		}

		showScanningUI('读取本地已有文件...');
		// Tasks loaded from IndexedDB carry their own quanpin, but tasks predating
		// the schema change won't — refresh addrMap so getQuanpin's fallback path
		// matches what the original run wrote.
		if (addrMap.size === 0) addrMap = await fetchAddrList();
		manifestCache = await readManifest();
		const manifestKeys = new Set(Object.keys(manifestCache));

		showScanningUI('标记全部未读...');
		await markAllUnread();

		let skipped = 0;
		for (const task of pending) {
			const key = buildManifestKey(task);
			if (manifestKeys.has(key)) {
				task.status = 'done';
				await dbPut('tasks', task);
				skipped++;
			}
		}

		if (skipped > 0) {
			updateScanMessage(`跳过 ${skipped} 个已有文件，同步已读状态...`);
			await syncReadStatus(allTasks);
		}

		const actualPending = pending.filter(t => t.status === 'pending');
		const actualDone = total - actualPending.length;

		if (actualPending.length === 0) {
			showProgressUI(actualDone, total, 0, mc);
			return;
		}

		showProgressUI(actualDone, total, 0, mc);
		const tracker = createProgressTracker(total, actualDone);
		await startEngine(actualPending, task => tracker.onTask(task));

		// resume 不重生成 report.md，但重复索引贴在文件旁，每次都从 allTasks 重派——成本低。
		await tagDuplicateMails(allTasks);
		await writeDuplicateIndex(allTasks);
	}

	async function retryFailed(failedTasks) {
		if (!rootHandle) {
			try {
				rootHandle = await window.showDirectoryPicker({ mode: 'readwrite' });
			} catch (e) {
				return;
			}
		}

		const currentSid = getSidFromUrl();
		for (const t of failedTasks) {
			// If sid is missing (e.g. user navigated to a page without sid), keep the old URL
			// and let the engine's session-expiry recovery kick in instead of writing sid=null.
			if (currentSid) t.url = replaceSid(t.url, currentSid);
			t.status = 'pending';
			t.error = undefined;
		}
		await dbPutBatch('tasks', failedTasks);

		const allTasks = await dbGetAll('tasks');
		const doneCount = allTasks.filter(t => t.status === 'done').length;
		const total = allTasks.length;
		const mailCount = new Set(allTasks.map(t => t.mailid)).size;
		showProgressUI(doneCount, total, 0, mailCount);

		// Tracker now handles base-offset internally — drop the old onTask hack.
		const tracker = createProgressTracker(total, doneCount);
		await startEngine(failedTasks, task => tracker.onTask(task));

		const section = document.getElementById('__dl_fail_section');
		if (section) {
			const remaining = failedTasks.filter(t => t.status === 'failed');
			if (remaining.length === 0) {
				section.innerHTML = '';
			}
		}
	}

	// ============================================================
	//  Init
	// ============================================================

	async function init() {
		if (!window.showDirectoryPicker) return; // FSAPI required
		sid = getSidFromUrl();
		folderId = getFolderIdFromUrl();
		folderName = '';
		if (!sid || !folderId) return;

		db = await openDB();
		setupAutoSidRecovery();

		const existing = await dbGetAll('tasks');
		const folderTasks = existing.filter(t => t.folderId === folderId);
		if (folderTasks.length > 0) {
			const pending = folderTasks.filter(t => t.status === 'pending' || t.status === 'failed');
			if (pending.length > 0) {
				showResumeUI(pending.length);
				return;
			}
		}

		showStartUI();
	}

	// Handle SPA navigation (QQ Mail uses hash-based routing)
	window.addEventListener('hashchange', () => {
		const newFolderId = getFolderIdFromUrl();
		if (newFolderId && newFolderId !== folderId) {
			folderId = newFolderId;
			sid = getSidFromUrl();
			const old = document.getElementById('__dl_panel');
			if (old) old.remove();
			init();
		}
	});

	// @run-at document-idle guarantees DOM is ready
	setTimeout(init, 1000);
})();
