#!/bin/bash
# 双击这个文件即可启动幸存者服务器（会打开一个终端窗口）
# 关闭服务器：在这个终端窗口里按 Control + C

cd "$(dirname "$0")" || exit 1

if ! command -v python3 >/dev/null 2>&1; then
  echo "没有找到 python3，请先安装 Python 3。"
  echo "按回车关闭…"
  read -r _
  exit 1
fi

echo "正在启动服务器…（地址见下方，手机需连同一个 Wi-Fi）"
python3 server.py "$@"

echo
echo "服务器已停止。按回车关闭窗口…"
read -r _
