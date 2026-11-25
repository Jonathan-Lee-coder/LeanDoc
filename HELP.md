# Git 使用指南（本机 / D:\LeanDoc）

## 建仓库：第一次在 GitHub 上建一个空仓库（5 步）

1. 浏览器打开 <https://github.com/new>，确认已登录**你自己的**账号。
2. **Repository name** 填仓库名，例如 `LeanDoc`（建议和本地目录名一致）。
3. 选 **Public**（公开才满足"别人 clone 后 `lake build` 就能复核"；想先私有就选 **Private**，之后随时可改）。
4. **不要**勾 "Add a README file" / "Add .gitignore" / "Choose a license"——保持**全空**。勾了会先在远端产生一个 commit，你本地首次 push 会因 `non-fast-forward` 失败，还得 `git pull --allow-unrelated-histories`。
5. 点 **Create repository**。建好后页面会显示 `https://github.com/<你的用户名>/<仓库名>.git`，这就是 §6 里 `git remote add origin` 要填的地址。`你的用户名` 是 GitHub **登录名**（打开 github.com 点头像 → *Your profile*，地址栏 `github.com/` 后面那段），不是显示昵称。

建好之后：按 §1 设身份 → `git branch -m main`（本仓库当前叫 `master`，本文其余部分都按 `main` 写）→ §6 连远端、推第一次。`git add` 时别带上 `_*.log`、`.paper.txt` 这类临时文件（见 §8）。

---

## 0. 现在装好了什么

| 组件 | 位置 | 版本 |
| --- | --- | --- |
| Git | `C:\Program Files\Git\cmd\git.exe` | 2.56.1.windows.1 |
| VSCode | `D:\VSCode\Microsoft VS Code` | 已装 `leanprover.lean4` 0.0.242 |
| Lean / elan / lake | `C:\Users\JonathanLee\.elan\bin` | Lean 4.36.0（项目用 4.37.0-rc1） |

**必须先重启 VSCode。** VSCode 只在进程启动时读一次 PATH，新装的 Git 对已经开着的窗口不可见。
彻底退出（不是关窗口，是退出进程）再打开 `D:\LeanDoc`，左侧"源代码管理"图标才会亮。
如果仍提示找不到 git，在设置里加一行 `"git.path": "C:\\Program Files\\Git\\cmd\\git.exe"`。

---

## 1. 一次性配置（你还没做过，必做）

你这台机器**没有** `~/.gitconfig`，所以现在 commit 会失败。跑一次：

```bash
git config --global user.name  "你的名字"
git config --global user.email "you@example.com"
git config --global init.defaultBranch main
git config --global core.autocrlf input      # 提交时统一 LF，避免 Windows 换行污染
git config --global pull.rebase true
```

检查配置来自哪个文件：

```bash
git config --list --show-origin
```

`core.autocrlf input` 的意思：工作区保留 CRLF 不影响，但**写进仓库的一律是 LF**。
Git for Windows 默认是 `true`（会把检出文件变成 CRLF），对 Lean 源码无害，但跨平台项目里容易出脏 diff。

---

## 2. 四个基本动作

`D:\LeanDoc\.git` 我已经帮你建好了，`.gitignore` 也已写好（**排除了 `.lake/`**，那是几 GB 的 mathlib 编译产物，绝不能提交）。

```bash
git status                        # 现在什么状态：改了什么、暂存了什么
git add DLMST/Recurrence.lean     # 暂存指定文件（别用 git add -A 闭眼全加）
git commit -m "prove recurrence_linear"
git log --oneline --graph --decorate -10
```

工作模型一句话：**工作区 →（add）→ 暂存区 →（commit）→ 仓库**。`git status` 的输出会把这三层直接写给你看，迷路了就跑它。

---

## 3. VSCode 里怎么做

1. `Ctrl+Shift+G` 打开源代码管理面板
2. "_changes_" 列表里每个文件右侧有 `+`（暂存）；暂存后在上方输入框写 message，`Ctrl+Enter` 提交
3. 点任意文件名 → 打开左右对照 diff
4. 面板右上角 `⋅⋅⋅` 菜单：amend、stash、创建分支、discard changes 都在里面
5. 资源管理器最底部的"时间线"= 该文件的历史
6. 建议装 **Git Graph**（`.vscode/extensions.json` 已推荐，打开 VSCode 会提示安装），能看到分支拓扑

---

## 4. 分支

```bash
git switch -c try-schedule-lemma   # 新建并切换（最常用）
git switch main                    # 切回主分支
git branch                          # 列出所有分支，* 是当前
git merge try-schedule-lemma       # 把它并进当前分支
git branch -d try-schedule-lemma    # 删除已合并的分支（安全，未合并会拒绝）
git branch -D try-schedule-lemma    # 强制删除（危险）
```

经验法则：**证明写到一半、不确定能不能跑通，就开分支**。跑通再 merge，跑不通直接 `-D`，主分支干干净净。

---

## 5. 撤销（从安全到危险）

```bash
git restore --staged file.lean   # 取消暂存，改动还在          【安全】
git restore file.lean            # 丢弃工作区改动               【不可逆，先确认】
git commit --amend -m "新信息"    # 改最近一次提交（还没 push 时才安全）
git reset --soft HEAD~1          # 退回一次提交，改动留在暂存区 【安全】
git reset --mixed HEAD~1         # 退回一次提交，改动留在工作区 【较安全】
git reset --hard HEAD~1          # 退回并丢弃所有改动           【危险】
git revert <commit-sha>          # 生成一个"抵消"提交           【已 push 时用这个】
```

**真丢了东西怎么找回：**

```bash
git reflog                 # 记录 HEAD 走过的每一步，救命命令
git stash list             # 看有没有存起来的东西
```

`git reset --hard` 之后只要提交过，`git reflog` 找到那个 sha，再 `git reset --soft <sha>` 就能拿回来。
**没提交过的改动，任何工具都救不了**——所以勤 commit。

临时收起来（比如要切分支但代码是半成品）：

```bash
git stash push -u -m "wip: scheduling lemma"
git stash pop
```

---

## 6. 连 GitHub

```bash
git remote add origin https://github.com/你的用户名/仓库名.git
git remote -v                       # 确认
git push -u origin main             # 第一次推，-u 建立跟踪关系
git pull                            # 之后就是 pull / push
```

GitHub 早已不支持账号密码，需要 **Personal Access Token**（Settings → Developer settings → Tokens，勾 `repo` 权限）或直接配 SSH key。VSCode 会弹窗让你登录 Microsoft 账号，一般照做即可。

**网络**：你的代理是 `127.0.0.1:7890`。git 不读 Windows 系统代理，push/pull 卡住时二选一：

```bash
# 临时（推荐，不改动配置）
http_proxy=http://127.0.0.1:7890 git push

# 持久
git config --global http.proxy  http://127.0.0.1:7890
git config --global https.proxy http://127.0.0.1:7890
git config --global --unset http.proxy    # 不用时记得关掉
```

---

## 7. 和 Lean 项目配合的用法

```bash
lake build                                   # 编译整个项目（含 DLMST 六个文件）
lake env lean DLMST/VectorMaxima.lean        # 只编译一个文件，报错信息最直接
```

推荐节奏：

- **证完一条 lemma 就一次 commit**，message 写"证了什么"或"试了 X 路径，卡在 Y"——半年后你会感谢自己
- 探索性写法放分支，`.lake` 永远不进仓库；换电脑靠 `lake update && lake exe cache get` 重建依赖
- 想公开给他人验证时，把 `DLMST/*.lean` 推到 GitHub，别人 clone 后 `lake build` 就能复核——这才是形式化验证的意义

---

## 8. 不要提交的东西

- `.lake/`（已在 `.gitignore` 里）
- `.setup/`（安装 Lean 时的临时下载）
- 任何 token、密码、`*.env`
- 编译产物 `*.olean`
- 临时草稿与日志：`.paper.txt`、`_paper*.txt`、`_*.log`、`DLMST/_Probe.lean`（论文全文与构建日志，`git add` 时逐个点名文件，别用 `git add .`）
