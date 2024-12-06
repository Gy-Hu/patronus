# 拉取 upstream 的最新更新
git fetch upstream

# 获取本地所有分支（包括远程分支）
for branch in $(git branch -r | grep 'upstream/' | sed 's/upstream\///'); do
    echo "Updating branch $branch"
    
    # 切换到本地分支，如果没有就创建
    git checkout -B $branch upstream/$branch

    # 推送到远程仓库
    git push origin $branch --force
done
