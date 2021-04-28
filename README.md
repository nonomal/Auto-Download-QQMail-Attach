支持Mac和Windows系统，支持腾讯企业邮箱。  
https://zhuanlan.zhihu.com/p/51543237
  
## 批量下载QQ邮箱附件，下载完后修改文件重命名

因为工作原因，需要处理QQ邮箱来自各地网友的投稿附件。数量比较多（上千份），如果手动一个一个下载非常麻烦。。。

而且有些发来的附件命名也不规范，下载下来之后还需要手动去重命名，否则放一起就分不清谁是谁了，还可能会出现大量重复的命名文件。 这种非常机械化的重复操作，我想写个脚本批量下载QQ邮箱附件。

网上搜了下资料，基本都是通过POP3来下载，但这个邮箱并不是自己的，只是临时注册用来接收邮箱的小号，对方也不希望开通手机认证。

于是临时研究了一下 Python + selenium + Chrome 来模拟手动爬虫~
  
--

<br>  

## 如何安装

### MAC

如果你是MAC用户。操作相对简单一些：

1. **Homebrew**  
https://brew.sh/index_zh-cn

简单的说，就是把下面这段指令复制粘贴到终端(Terminal)
```
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"
```

<br>  

2. **python3 + helium**  
简单的说，就是把下面这段指令复制粘贴到终端(Terminal) 

```
brew install --cask chromedriver
brew install --cask helium
brew install --cask chromedriver
```

<br>   
     
### Windows
Windows 用户安装稍微复杂一点点，不过大家都习惯了这些蛋疼的操作了吧：

1. **Python 3**   
https://www.python.org/  

> 下载最新版即可，跟着引导安装，点页面中那两个带着小盾牌图标的大按钮。
> - [x] 1. Install Now
> - [x] 2. Disable path length limit

<br>   
     
2. **pip install x**  
如果你已经安装好了 python 环境，按下 Win + R，输入 cmd，打开控制台。    
接着输入下方的指令：

```
pip install selenium
pip install helium
pip install prettytable
```

<br><br> 

<details><summary>WebDriver for Chrome （可跳过）</summary>

<br>   
     
**WebDriver for Chrome**  
https://sites.google.com/a/chromium.org/chromedriver/downloads
    
因为现在用了 helium 模块，所以已经不需要再手动安装 chromedriver，因此可以省略此步骤。  
但还是把安装方法留着吧，也许以后有路人用的上。

<br>

> 注1：  
> **下载对应版本号**：  
> 比如你Chrome 版本是 90.0，就下载 90.0 版本。  
> 以后浏览器有更新，也是需要重新下载对应版本的 chromedriver。否则会报错。  
>   
> 注2：
> **如何查看 Chrome 当前版本号**：  
> 右上角 - 设置 - 关于Google Chrome 
>   
> 注3：
> **如何安装（环境变量）**：    
> 下载好之后，把 chromedriver.exe 放到随意一个文件夹，然后复制当前这个文件夹的路径。  
> 通常我喜欢把这类工具专门放到一个叫 bin 的文件夹里。比如 ` D:\Program\bin `
>   
> 按下 Windows 键，输入 path ，会看到一个「编辑系统环境变量」，按下回车就能打开它。  
> 打开右下角「环境变量」，在下面「系统变量」列表里，找到 Path 一行，双击编辑。  
> 右上角有「新建」，它会在列表后面新建空的一行，接着把刚才的文件夹路径粘贴进去就可以了。
   
</details>  
 
<br><br>  
  
好了，繁琐的前置工作完成了。接着可以正式开始咯。  

<br>
   
## 在开始之前，你需要先做几件事。

#### 1 邮箱文件夹

把你想要下载的邮件**移动到**文件夹里，方便整理区分。
   
<br>   
   
### 2 邮箱文件夹的编号
在左侧的面板‘我的文件夹’中找到你刚刚创建的文件夹，  
然后**右键-新窗口打开**，在浏览器地址栏的网址链接找到**文件夹ID**的参数:  `folderid`  
  
举例：这里的 folderid={ A }，里面通常是一个数字，例如：123，129，200...  
```
https://mail.qq.com/cgi-bin/frame_html?t=frame_html&sid={x}&url=/cgi-bin/mail_list?folderid={ A }%26page={x}
```  
     
<br>   
   
### 3 邮箱设置

不知道你们平时邮箱设置是什么情况，我先说说我的吧：  
1.可选：每页显示 100 封邮件。（虽然脚本会自动翻页，但显示多一些会更方便）  
2.可选：关闭显示邮件摘要，邮件大小。（虽然开了也没关系，因为完全没有处理这些。但页面显示的内容越少，脚本处理速度会更快）  
3.重要：邮件列表视图选择**标准模式**。（因为我没用过会话模式，当然，会话模式的好处就是可以收件人去重，我只是拿他来查看有多少人投稿)   
4.根据需要：新建标签 [没有附件], [过期附件]，如果你用得上，脚本会自动帮你分类加标签。

<br><br><br>
    
## 如何使用

已经安装了 Python，会发现开始菜单新增了一个 IDLE 编辑器，从菜单新建文件：File - New File (Ctrl + N)。    
然后把 [QQMail.py](https://raw.githubusercontent.com/XHXIAIEIN/Auto-Download-QQMail-Attach/master/QQMail.py) 的代码复制粘贴到 IDLE 中，  
将文件保存在任意位置(比如桌面)，随便取个名比如 QQmail.py  
    
阅读前半部分的参数区，根据你的需要对参数进行修改。具体的参数说明请继续看下方。    
当你想运行脚本时，只需要在 IDLE 中运行代码即可：Run - Run Module (F5)   
  
  
<br>   
   
> 注：通过运行脚本启动的浏览器窗口，只能同时启动一个。若重复启动脚本将会打开空页面，需要关闭上一个窗口重新运行脚本。  
     
<br><br><br>  
   
### 修改自定义参数

主要有几个参数需要修改：  

1. **邮箱登录账号**（必填）  
请放心填，没人能偷看你屏幕。。

```
QQNUMBER="132465798"  
PASSWORD="132465798"
```
  
如果是企业邮箱，需要填到企业邮箱的位置。  
  
   
<br><br>  
    
2. **附件下载路径**（必填）  
浏览器下载的文件会自动保存在这里。只需要填 ` ROOTPATH `， 剩下两个会在这个目录创建文件夹。  
> 注：Win系统路径需要以 \\\ 作为分隔。如：` DOWNLOAD_FOLDER='D:\\Downloads\\' `     
>     MAC系统则需要 / 作为分隔符。 
```
ROOTPATH = "D:\\Downloads\\2020"
DOWNLOAD_FOLDER = os.path.join(ROOTPATH,"download")     # 不需要修改。附件实际下载目录 即："D:\\Downloads\\2020\\download"
USERDATA_FOLDER = os.path.join(ROOTPATH,"selenium")     # 不需要修改。浏览器的缓存数据 即："D:\\Downloads\\2020\\selenium"
```   
  
<br><br>  
  
  
3. **文件夹ID**（必填）  
就如前面的提示， 在文件夹右键，新窗口打开，找到网址链接的参数
```
https://mail.qq.com/cgi-bin/frame_html?t=frame_html&sid={x}&url=/cgi-bin/mail_list?folderid={ A }%26page={x}
``` 
  
<br><br>  
  
4. **计划任务** （可选） 
- Title_Task，从第几封邮件开始，只读取多少封邮件，或者在第几封邮件结束。  
- Pages_Task，从第几页开始，翻多少页后结束，或者在第几页结束。   
 
> start  从第几个开始。默认从第1封邮件开始。    
> end    到第几个结束。举例：执行到第 20 封邮件时结束。(包含第20封邮件)   
> step   执行多少次后结束。举例：从第 1 封邮件开始执行，往后处理 10 封结束，也就是在第 10 封邮件时结束下载。   

注：end 和 step 不同的地方是，end 代表着结束的终点，而 step 则是从开始后累计的数量。  

```
Title_Task = { 'start':1, 'step':0, 'end': 0 }
Pages_Task = { 'start':1, 'step':0, 'end':0, 'autoNext': 1 }
```
  
<br><br>    
  
  
5. **关键词过滤：邮件主题** （可选）   
TITLE_BACKLIST_KEYS，黑名单  
TITLE_WHITELIST_KEYS，白名单  

需要注意的是，白名单关键词越多，匹配规则越严格。
      
``` 
TITLE_WHITELIST_KEYS = ['反馈','2020']      # 只处理标题同时包含这两个关键词的邮件
TITLE_BACKLIST_KEYS  = ['发信方已撤回邮件']  # 不处理
```
  
<br><br>    
  
6. **文件类型过滤：附件** （可选）   
ATTACH_BACKLIST_FILETYPE，黑名单  
ATTACH_WHITELIST_FILETYPE，白名单  
      
``` 
attach_blacklist_filetype = [''] 
attach_whitelist_filetype = ['psd', 'ai']  # 不下载 psd 或 ai 类型的文件
```
  
<br><br>    
  
7. **Config 高级参数** （可选）
脚本中还提供了一些高级选项，可以根据实际需要来开启或关闭。  
通常修改参数为 1 或 0

```python

# 浏览器禁用显示图片，（浏览器首次运行前生效）
can_disabled_images = 0

# 是否倒序读取（从最后一页开始往前）
can_reverse_list = 0

#··········· 下载 ···········#

# 是否需要重命名附件
can_rename_file = 0

# 是否需要每封邮件创建文件夹
can_move_folder = 1

# 在下载前，检查本地文件是否已存在附件（根据文件名+文件大小）
# 如果存在则跳过本次下载。
ready_download_but_file_exists = 'skip' or 'continue'


#··········· 星标 / 标签 ···········#

# 没有附件的邮件设为星标
can_star_nofile = 1
 
# 过期附件的邮件设为星标
can_star_timeoutfile = 0
 
# 没有附件添加标签
can_tag_nofile = 0
str_tag_nofile = '没有附件'
 
# 过期附件添加标签
can_tag_timeoutfile = 0
str_tag_timeoutfile = '过期附件'


#··········· 功能 ···········#

# 是否需要下载附件
can_download_file = 1

# 是否需要进入邮件正文
can_load_email = 1

# 是否需要获取邮件标题列表
can_load_title = 1

# 下载等待时长(单位：秒)。超过时长后则放弃后续操作，如移动文件夹或重命名。
downloading_timeout = 300


#··········· 控制台 ···········#
 
 # 是否需要 PrettyTable 来打印表格  
 # 如果有人装不上 PrettyTable，可以将它禁用。
 can_print_prettytable = 1
 
# 是否在控制台打印邮件信息
can_print_title = 1
can_print_attch = 1
 
# 是否在控制台打印统计表格
can_print_folder_table = 1
can_print_title_table = 1


#··········· 统计 ···········#

# 是否将数据导出为CSV文件
can_export_titledata_to_csv = 1
can_export_attchdata_to_csv = 1


#··········· 高级选项 ···········#

# 是否需要设置 desired_capabilities 参数
can_set_capabilities = 1
config_timeout_pageLoad = 10000
config_timeout_script = 1500

```
  
<br><br>    
  
8. **重命名模板** （可选）     
如果需要添加其他变量，可以自己修改脚本。搜索 `rule = `
```python
#-------------------------------------------------------------------------------
# 重命名模板
#-------------------------------------------------------------------------------
# filename1       附件文件名(不包含扩展名）              例: 简历
# filename2       附件文件名(包含扩展名）                例: 简历.pdf
#···············································································
# extension1      附件扩展名(包含.)                      例: .jpg  .txt  .pdf
# extension2      附件扩展名(不包含.)                    例:  jpg   txt   pdf
#···············································································
# attchindex      计数：目前是第几个附件（不包含过期附件）          例:  0001
# titleindex      计数：目前是第几封邮件 (从1开始计数)              例:  0001
# pageindex       计数：目前是第几页 (从1开始计数)                  例:  001
# attchtitleindex 计数：在当前邮件中的多个附件的顺序 (从1开始计数)  例:  01
#···············································································
# titlecount      总数：本次下载计划的邮件数量                      例:  0
# attchcount      总数：本次下载计划的附件数量（包含过期附件）      例:  0
#···············································································
# folderid        文件夹：folder_id                      例:  129
# foldername      文件夹：名称                           例:  我的文件夹
# foldertitle     文件夹：邮件数量                       例:  500
# folderpage      文件夹：总页数                         例:  20
#···············································································
# nameid          发信方的邮箱昵称                       例:  小明
# address         发信方的邮箱地址                       例:  123456@qq.com, xiaomin233@vip.qq.com
# emailid         发信方的邮箱账号，通常是QQ号           例:  123456, xiaomin233
#···············································································
# year            发送时间：年  %Y                       例:  2020
# month           发送时间：月  %m                       例:  12
# day             发送时间：日  %d                       例:  07
#···············································································
# week            发送时间：周  %a                       例:  Mon 
# ampm            发送时间：上/下午 %p                   例:  AM
#···············································································
# hours           发送时间：时  %H                       例:  14 
# minutes         发送时间：分  %M                       例:  30 
# seconds         发送时间：秒  %S                       例:  59 
#···············································································
# time1           发送时间：格式化  %H%M                 例:  1430
# time2           发送时间：格式化  %H-%M-%S             例:  14-30-59
# time3           发送时间：格式化  %H'%M'%S             例:  14'30'59
#···············································································
# date1           发送时间：格式化  %m%d                 例:  1207
# date2           发送时间：格式化  %Y%m%d               例:  20201207
# date3           发送时间：格式化  %Y-%m-%d             例:  2020-12-07
#···············································································
# fulldate1       发送时间：格式化  %Y-%m-%d_%H-%M-%S    例:  2020-12-07_14-30-59
# fulldata2       发送时间：格式化  %Y%m%d_%H'%M'%S      例:  20201207_14'30'59
#···············································································

# 需要放到花括号里。例如 {attchindex}_{filename2} => 0001_作品.pdf

# 附件重命名规则。
# 案例：{attchindex}_{filename2} => 0001_作品.pdf
rule_rename = "{attchindex}_{filename2}"     
 
# 文件夹名称。
# 案例：{address}({date4}) => 0001_123456@qq.com_2020-12-07_14-30-59
rule_folder = "{titleindex}_{address}_{fulldate1}"

```
  
<br><br><br>  
  
  
## 特性

**下载**
- 自定义附件的下载路径。  
- 自定义浏览器缓存的路径。
- 下载后：可以按每封邮件主题，根据命名规则新建文件夹。
- 下载后：可以按每个附件，根据命名规则重命名。
- 下载前：检查文件是否已存在于文件夹。(判断方式：文件名和附件大小相同) 
- 关键词过滤：附件扩展名的白名单/黑名单。只下载某些文件类型，或跳过某些文件类型的附件。
  
**等待**
- 如果页面提示"请求速度过快"，脚本会自动等待，并自动刷新页面，直到恢复正常。
- 等待下载完成：如果需要下载完成后分类文件，脚本会等待文件下载完成，再根据规则分类。
  
**登录**  
- 填写账号密码，自动登录。  
- 支持腾讯企业邮箱
- 若出现滑块验证，会等待用户手动操作完成。  
- 若出现短信验证，用户可以尝试先登陆QQ客户端，然后使用快捷登陆点击头像。

**邮件**
- 自动翻页：自动点击下一页
- 关键词过滤：邮件标题的白名单或黑名单，过滤某些包含特定关键词的邮件标题。
- 任务计划：从文件夹第几页开始，到第几页结束，或者只处理多少页结束。
- 任务计划：从文件夹第几封邮件开始，到第几封邮件结束，或者处理多少封邮件后结束。
- 没有附件：如果邮件没有包含附件，或者附件已过期，可以标记星标或者添加标签。

**统计**
- 脚本结束后会生成csv文件，包含所有**邮件**列表信息。  
- 脚本结束后会生成csv文件，包含所有**附件**列表信息。  

  
<br>  <br>  
  
## 可能出现的问题

1. 如果网络异常，浏览器可能提示下载失败，但脚本会长时间等待它下载完成，或者超过5分钟后，脚本也会将它跳过。  
> 解决方案：如果发现下载失败，可以手动在浏览器底部的下载提示中继续执行。
  
<br>  

2. 如果邮箱没有设置过标签，邮箱主页的左侧面板会自动隐藏这个栏目。此时如果启用脚本设置的自动添加标签功能，可能会报错。
> 解决方案：给邮箱创建至少一个标签。例如：“过期”，“没有附件”  
<br>   

3. 如果不禁用显示图片，在下载附件时会非常非常非常慢！！
> 解决方案：在第一次运行脚本时，先显示图片用于登陆验证。登陆成功后浏览器已经有自动缓存，此时再禁用显示图片用于下载。
  
<br>  

## 踩坑历史

1. 附件收藏中的"全部附件"，并不是想象中真的把全部附件整合在一起，还是会漏掉一些，关键是还不知道漏了哪些。    
> 解决方案：脚本的下载方式是模拟手动读取邮件下载附件，不是从"全部附件"下载的。  
  
<br>   
  
2. 在下载过程中，中途收到了新的邮件，列表顺序会出现错误。  
> 解决方案：不要直接下载收件箱的邮件。将他们移动到一个新的文件夹中下载，确保在脚本执行过程邮件列表不要有变化，如果开启了移动到此文件夹的收件规则请记得关闭。  
  
<br>   
  
3. 如果长时间没有在QQ客户端登录过账号，会提示非常用设备异常登录，需要短信验证。    
> 解决方案：先在QQ客户端登录账号，再运行脚本，登录页面会出现快速登陆的头像。记得勾选"下次自动登陆"，下次就会直接进入邮箱主页了。  
  
<br>   
  
4. 对方发送的"超大附件"会过期，无法下载。  
> 解决方案：超大附件(bigattach="1")有一个参数("timeout"= 0 or 1)是普通附件(attach="1")没有的。  
> 如果检测到邮件中包含过期附件，脚本会自动跳过，并且自动标记为星标邮件，或者添加"过期附件"的标签。  
  
<br>   

5. 如果开启了[自动重命名]功能，最终命名时会出现错位情况。下载的第一个文件的命名变成了第二个，第二个变成第三个....
>  解决方案：开车速度过快，上个文件还没下载完就开始处理下一个文件了。因此降低了处理速度，让它慢下来。（现在处理每个文件的时间大概多出了2.5秒）
  
<br>   

2. 如果开启了[按邮件新建文件夹]或[自动重命名]功能，附件名包含空格字符，可能会导致脚本崩溃。  
> 临时解决方案：据说只是因为脚本文件没有声明编码？我试着在文件头部加了2行，实际效果效果待测试。
  
  
  
<br><br><br>   


# 小伙子，你干得不错！

如果你觉得这个脚本对你非常有帮助，节省了你的时间，提升了你的工作效率....
可以请我喝杯咖啡喔！我会非常高兴的！！

![xhxiaiein_sponsors](https://user-images.githubusercontent.com/45864744/116388661-a2f7db00-a84e-11eb-9f05-f058aea6222c.png)

