#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""配布用の exe とフォルダ一式を作る。

Python もターミナルも触らない人に渡すためのもの。
出来上がった `配布/国道走破マップ/` をそのまま zip にして渡せばよい。

    python build_exe.py

PyInstaller だけは必要（`python -m pip install pyinstaller`）。
これは**作るときだけ**の道具で、出来上がった exe には何も要らない。
kokudo_map.py 自体は標準ライブラリしか使っていない。

渡す相手のパソコンに Python は要らない。Windows 用の exe が出来る
（Mac 用が要るなら Mac の上で同じコマンドを走らせること。
  PyInstaller は動かしたOS向けの実行ファイルしか作れない）。

cache/derived/ は入れない。165MB あるうえ、渡された人の環境で
最初に地図を開いたときに作り直される。
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
APP_NAME = "国道走破マップ"
OUT_DIR = os.path.join(BASE_DIR, "配布")
PKG_DIR = os.path.join(OUT_DIR, APP_NAME)
WORK_DIR = os.path.join(OUT_DIR, "_作業")

# 渡す人向けの説明。exe と同じ場所に置く。
GUIDE = """国道走破マップ

■ 使いかた

  「{app}.exe」をダブルクリックしてください。
  黒い画面が少し出たあと、ブラウザに地図が開きます。
  （初回だけ、地図のデータを整えるのに十数秒かかります）

  ・赤い道 … 走ったところ
  ・青い道 … まだ走っていないところ

  地図を拡大すると交差点の名前が出ます。
  名前を押して「ここから」、もう一方の名前を押して「ここまで」を選ぶと、
  その区間が走破として記録されます。
  名前の無いところでも、道の線そのものを押せば区間の端にできます。

  右側の「道の駅を出す」を入れると星印が出ます。
  星を押して「行った」を押すと、訪問した記録になります。

■ 終わりかた

  地図の右上にある「終了」を押してください。黒い画面も自動で閉じます。
  ブラウザのタブを閉じるだけでも、少ししてから自動で終わります。

■ 記録の場所

  走った記録は、このフォルダの中の routes.csv に入っています。
  道の駅の記録は michinoeki.csv です。どちらも Excel やメモ帳で開けます。

  このフォルダごと保存しておけば、新しいパソコンに移しても記録は残ります。
  （逆に、フォルダを消すと記録も消えます）

  記録の修正と削除は、地図の右側「走破記録」タブからもできます。

■ 注意

  ・cache フォルダは地図のデータです。消すと地図が出なくなります。
  ・初回は「WindowsによってPCが保護されました」と出ることがあります。
    「詳細情報」→「実行」で進めてください。
    （作った人が有料の署名を持っていないためで、中身の問題ではありません）
  ・インターネットに繋がっていなくても、記録と地図は使えます。
    背景の地図（国土地理院）だけは繋がっていないと出ません。

  道路データ・交差点名・道の駅: (c) OpenStreetMap contributors
    Open Database License (ODbL) https://www.openstreetmap.org/copyright
  背景地図: 国土地理院タイル
""".format(app=APP_NAME)


def run(cmd):
    print("  $ " + " ".join(cmd))
    r = subprocess.run(cmd)
    if r.returncode != 0:
        sys.exit(f"失敗しました（終了コード {r.returncode}）")


def copy_cache(src, dst):
    """地図のデータを複製する。導出データ（作り直せる）は入れない。"""
    shutil.copytree(src, dst, ignore=shutil.ignore_patterns("derived"))


def main():
    try:
        import PyInstaller  # noqa: F401
    except ImportError:
        sys.exit("PyInstaller がありません。\n"
                 "  python -m pip install pyinstaller\n"
                 "を実行してから、もう一度試してください。")

    cache = os.path.join(BASE_DIR, "cache")
    if not os.path.isdir(cache):
        sys.exit("cache フォルダがありません。\n"
                 "  python kokudo_map.py fetch --all\n"
                 "で地図のデータを揃えてから、もう一度試してください。")

    print("1. exe を作ります（数分かかります）")
    if os.path.isdir(WORK_DIR):
        shutil.rmtree(WORK_DIR, ignore_errors=True)
    run([sys.executable, "-m", "PyInstaller",
         "--onefile",                 # 1つの exe にまとめる
         "--console",                 # 進み具合と、うまくいかないときの理由を出す
         "--noconfirm",
         "--clean",
         "--name", APP_NAME,
         "--distpath", WORK_DIR,
         "--workpath", os.path.join(WORK_DIR, "build"),
         "--specpath", WORK_DIR,
         os.path.join(BASE_DIR, "kokudo_map.py")])

    exe = os.path.join(WORK_DIR, APP_NAME + (".exe" if os.name == "nt" else ""))
    if not os.path.exists(exe):
        sys.exit(f"exe が見つかりません（{exe}）")

    print("2. 配る形にまとめます")
    if os.path.isdir(PKG_DIR):
        shutil.rmtree(PKG_DIR)
    os.makedirs(PKG_DIR)
    shutil.copy2(exe, PKG_DIR)

    # 地図のデータ。これが無いと何も出ない
    print("   cache/ を複製しています…")
    copy_cache(cache, os.path.join(PKG_DIR, "cache"))

    # 記録は入れない。渡された人の地図が最初から赤く塗られてしまう
    with open(os.path.join(PKG_DIR, "はじめにお読みください.txt"),
              "w", encoding="utf-8-sig", newline="\r\n") as f:
        f.write(GUIDE)

    shutil.rmtree(WORK_DIR, ignore_errors=True)

    print("3. zip にまとめます")
    zip_path = shutil.make_archive(PKG_DIR, "zip", OUT_DIR, APP_NAME)

    size = sum(os.path.getsize(os.path.join(r, n))
               for r, _, ns in os.walk(PKG_DIR) for n in ns)
    print("\n出来ました")
    print(f"  フォルダ: {PKG_DIR}（{size / 1024 / 1024:.0f} MB）")
    print(f"  渡す用  : {zip_path}（{os.path.getsize(zip_path) / 1024 / 1024:.0f} MB）")
    print(f"\nこの zip を渡してください。相手は展開して、中の"
          f"「{APP_NAME}.exe」をダブルクリックするだけです。")


if __name__ == "__main__":
    main()
