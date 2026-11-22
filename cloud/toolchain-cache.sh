#!/usr/bin/env bash
# Cache the built toolchain so a cloud session does not rebuild it.
#
#   cloud/toolchain-cache.sh key       # print the cache key
#   cloud/toolchain-cache.sh fetch     # restore into $TC; exit 1 if no cache
#   cloud/toolchain-cache.sh publish   # upload what is in $TC
#
# The key hashes every patch in patches/ plus the pinned revisions in
# setup-toolchain.sh, so changing a patch changes the key and forces a rebuild:
# a cache can never hand back a binary built from different patches.
#
# Two places, tried in order:
#   1. GitHub release `toolchain-<key>`, asset toolchain.tar.zst (needs gh auth
#      to publish; anyone can download, the repo is public).
#   2. Orphan branch `toolchain-cache/<key>`, the tarball split into 90 MB parts
#      (GitHub refuses files over 100 MB).  Used when gh cannot publish.
# A restored toolchain still has to pass cells/verify/toolchain.sh, which
# setup-toolchain.sh runs afterwards either way.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
TC="${TC:-$HOME/dev2/lib/fpgatoolchain}"
SLUG="${SLUG:-jasonzeng124/asyncfpga3}"
WORK="${TMPDIR:-/tmp}/tc-cache.$$"

key() {
    { cat "$REPO"/patches/nextpnr-xilinx-*.patch
      grep -E '^[A-Z_]+_REV=|^PART=' "$REPO/cloud/setup-toolchain.sh"
      uname -m; . /etc/os-release 2>/dev/null; echo "${ID:-}-${VERSION_ID:-}"
    } | sha256sum | cut -c1-16
}
KEY=$(key)

need_zstd() { command -v zstd >/dev/null || { apt-get install -y -qq zstd >/dev/null 2>&1 || sudo apt-get install -y -qq zstd >/dev/null; }; }

pack() {  # -> $WORK/toolchain.tar.zst
    need_zstd; mkdir -p "$WORK"
    # Only what the flow reads: openxc7/ (without the chipdb importer's copy of
    # prjxray-db, which is only needed to regenerate the .bin, and without the
    # non-zynq7 families) and prjxray's python utils (fasm2frames).
    tar -C "$TC" -cf - \
        --exclude='openxc7/lib/external' \
        --exclude='openxc7/share/nextpnr/prjxray-db/artix7' \
        --exclude='openxc7/share/nextpnr/prjxray-db/kintex7' \
        --exclude='openxc7/share/nextpnr/prjxray-db/spartan7' \
        --exclude='openxc7/share/nextpnr/prjxray-db/virtex7' \
        --exclude='openxc7-src/prjxray/.git' --exclude='openxc7-src/prjxray/build' \
        openxc7 openxc7-src/prjxray \
      | zstd -T0 -12 -q -o "$WORK/toolchain.tar.zst"
    ls -la "$WORK/toolchain.tar.zst"
}

unpack() {  # stdin = tarball
    need_zstd; mkdir -p "$TC"
    zstd -dc | tar -C "$TC" -xf -
}

case "${1:-}" in
key) echo "$KEY" ;;

fetch)
    url="https://github.com/$SLUG/releases/download/toolchain-$KEY/toolchain.tar.zst"
    if curl -fsSL "$url" -o /dev/null -r 0-0 2>/dev/null; then
        echo "toolchain cache: release toolchain-$KEY"
        curl -fsSL "$url" | unpack
    elif git -C "$REPO" fetch -q --depth=1 origin "refs/heads/toolchain-cache/$KEY:refs/tc-cache" 2>/dev/null; then
        echo "toolchain cache: branch toolchain-cache/$KEY"
        parts=$(git -C "$REPO" ls-tree --name-only refs/tc-cache | grep '^part-' | sort)
        for p in $parts; do git -C "$REPO" cat-file blob "refs/tc-cache:$p"; done | unpack
        git -C "$REPO" update-ref -d refs/tc-cache
    else
        echo "toolchain cache: none for key $KEY"; exit 1
    fi
    echo "$KEY" > "$TC/openxc7/.cache-key"
    ;;

publish)
    pack
    if command -v gh >/dev/null && gh auth status >/dev/null 2>&1 \
       && gh release create "toolchain-$KEY" "$WORK/toolchain.tar.zst" -R "$SLUG" \
            --prerelease --title "toolchain $KEY" \
            --notes "Built by cloud/setup-toolchain.sh with every patch in patches/ (key = cloud/toolchain-cache.sh key). Not a project release." ; then
        echo "published release toolchain-$KEY"
    else
        echo "gh cannot publish a release; falling back to branch toolchain-cache/$KEY"
        d="$WORK/branch"; mkdir -p "$d"
        split -b 90M -d -a 3 "$WORK/toolchain.tar.zst" "$d/part-"
        git -C "$d" init -q; git -C "$d" checkout -q --orphan "toolchain-cache/$KEY"
        git -C "$d" add -A
        git -C "$d" commit -qm "toolchain cache $KEY (cloud/toolchain-cache.sh)"
        git -C "$d" push -q "$(git -C "$REPO" remote get-url origin)" "toolchain-cache/$KEY"
        echo "published branch toolchain-cache/$KEY"
    fi
    rm -rf "$WORK"
    ;;

*) sed -n '2,8p' "$0"; exit 2 ;;
esac
