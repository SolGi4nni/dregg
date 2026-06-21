#!/usr/bin/env bash
# Synthesized cross llvm-config: answers Mesa's queries from the aarch64-musl
# LLVM build tree ($CROSS_BUILD) without executing the target ELF binary.
CB="/tmp/llvm-cross-musl"
SRC_INC="/tmp/llvm-20.1.8.src/include"
HOST_LLVM_CONFIG='/opt/homebrew/opt/llvm@20/bin/llvm-config'
# Strategy: TARGET-INDEPENDENT metadata (--version, --components, module->lib name
# resolution) comes from the HOST llvm@20 (also 20.1.8, identical component model).
# TARGET paths (--prefix/--includedir/--libdir/--libs/--libfiles) point at the
# CROSS aarch64-musl build tree. So meson sees every module as PRESENT (host knows
# the component graph) but links the aarch64 .a files (cross libdir).
libdir="$CB/lib"; incdir="$CB/include"
H="$HOST_LLVM_CONFIG"
ver() { grep -m1 'LLVM_VERSION_STRING' "$CB/include/llvm/Config/llvm-config.h" 2>/dev/null | sed -E 's/.*"([0-9.]+)".*/\1/'; }
# Map requested component modules to the cross-built .a files: the HOST llvm@20
# (same 20.1.8, same component graph) expands the modules' link closure to lib
# basenames; we rebind each existing basename to $libdir (the aarch64 cross tree).
libs_cross() { # args: component modules
  "$H" --link-static --libnames "$@" 2>/dev/null | tr ' ' '\n' | while read -r b; do
    [ -n "$b" ] || continue
    [ -f "$libdir/$b" ] && printf '%s ' "$libdir/$b"
  done
}
# meson's LLVMDependencyConfigTool calls a COMBINED invocation, e.g.
#   llvm-config --libs --ldflags --link-static --system-libs <modules...>
# so we must scan ALL argv (order-independent): collect the flags present and the
# trailing module names, then emit the union in llvm-config's output order
# (libs, then ldflags, then system-libs). A single-query invocation (just one of
# --version/--prefix/...) is the degenerate case of the same scan.
WANT_LIBS=0; WANT_LDFLAGS=0; WANT_SYSLIBS=0; WANT_LIBFILES=0; WANT_LIBNAMES=0
SINGLE=""; MODULES=""
for a in "$@"; do
  case "$a" in
    --libs)        WANT_LIBS=1 ;;
    --libfiles)    WANT_LIBFILES=1 ;;
    --libnames)    WANT_LIBNAMES=1 ;;
    --ldflags)     WANT_LDFLAGS=1 ;;
    --system-libs) WANT_SYSLIBS=1 ;;
    --link-static|--link-shared|--ignore-libllvm) : ;;   # mode flags — no-op here
    --version|--prefix|--includedir|--libdir|--cppflags|--cflags|--cxxflags|--components|--shared-mode|--targets-built|--host-target|--build-mode|--assertion-mode|--has-rtti)
                   SINGLE="$a" ;;
    --*)           : ;;                                  # unknown flag — ignore
    *)             MODULES="$MODULES $a" ;;              # a component module name
  esac
done

# Single metadata query (no lib/ldflags/syslibs requested): answer it and exit.
if [ "$WANT_LIBS$WANT_LDFLAGS$WANT_SYSLIBS$WANT_LIBFILES$WANT_LIBNAMES" = "00000" ]; then
  case "$SINGLE" in
    --version) ver ;;
    --prefix) echo "$CB" ;;
    # BOTH includes: the build tree (generated llvm/Config/*) AND the source tree
    # (llvm-c/* + the non-generated llvm/* headers — not copied into the build tree).
    --includedir) echo "$incdir $SRC_INC" ;;
    --libdir) echo "$libdir" ;;
    --cppflags|--cflags|--cxxflags) echo "-I$incdir -I$SRC_INC -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -D_GNU_SOURCE" ;;
    --components) "$H" --components ;;
    --shared-mode) echo "static" ;;
    --targets-built) echo "AArch64" ;;
    --host-target) echo "aarch64-unknown-linux-musl" ;;
    --build-mode) echo "Release" ;;
    --assertion-mode) echo "OFF" ;;
    --has-rtti) echo "YES" ;;
    *) echo "" ;;
  esac
  exit 0
fi

# Combined link query: emit libs, then ldflags, then system-libs (llvm-config order).
# The LLVM static .a set is MUTUALLY RECURSIVE (e.g. ExecutionEngine<->RuntimeDyld<->
# Object<->...), so a single linker pass mis-orders them. Wrap them in
# -Wl,--start-group/--end-group so ld resolves cross-references across passes — the
# standard fix for static LLVM linking. (llvm-config's own --libs assumes a perfect
# topological order; the group makes order-independence explicit.)
out=""
if [ "$WANT_LIBFILES" = 1 ] || [ "$WANT_LIBS" = 1 ]; then
  LA="$(libs_cross $MODULES)"
  [ -n "$LA" ] && out="$out -Wl,--start-group $LA -Wl,--end-group"
fi
if [ "$WANT_LIBNAMES" = 1 ]; then out="$out $("$H" --link-static --libnames $MODULES 2>/dev/null)"; fi
if [ "$WANT_LDFLAGS" = 1 ]; then out="$out -L$libdir"; fi
if [ "$WANT_SYSLIBS" = 1 ]; then out="$out -lpthread -lm -ldl"; fi
echo "$out" | sed -E 's/^ +//;s/ +/ /g'
