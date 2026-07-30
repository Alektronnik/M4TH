#!/usr/bin/env bash
# =============================================================================
# M4TH.sh — Build & verification script for the M4TH monorepo
# =============================================================================
# Usage:
#   ./M4TH.sh all                Build all packages + compile all .live.lean + .web.lean files
#   ./M4TH.sh build              Build all packages via lake build
#   ./M4TH.sh build <Pkg>        Build a single package
#   ./M4TH.sh live               Compile all .live.lean files
#   ./M4TH.sh live <Pkg>         Compile .live.lean for a single package
#   ./M4TH.sh web                Compile all .web.lean files (v4.33.0-rc1 web version)
#   ./M4TH.sh web <Pkg>          Compile .web.lean for a single package
#   ./M4TH.sh clean              Remove M4TH.log
# =============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

LOGFILE="${SCRIPT_DIR}/M4TH.log"

# Overwrite log on each run
> "$LOGFILE"

# ── colour helpers ──────────────────────────────────────────────────────────
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BOLD='\033[1m'
NC='\033[0m' # No Colour

# ── header ──────────────────────────────────────────────────────────────────
log_header() {
    {
        echo "=============================================================================="
        echo " M4TH Verification Log"
        echo " Date   : $(date '+%Y-%m-%d %H:%M:%S')"
        echo " Lean   : $(lake --version 2>/dev/null || echo 'unknown')"
        echo " Commit : $(git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
        echo " Command: $0 $*"
        echo "=============================================================================="
        echo ""
    } | tee -a "$LOGFILE"
}

# ── package list ────────────────────────────────────────────────────────────
ALL_PKGS=(
    BurgersBlowUp
    CertifiedElliptic5077
    ConservationLaws
    DirichletEta
    DiscreteAbelChebyshev
    KdV
    MertensPNT
    Poincare4D
    PrimeGapsSophie
    SU3Concrete
    SU3Wilson
    XiArgumentPrinciple
    XiAsymptoticFrontier
    XiLogDeriv
    XiLogResidue
    ZetaZeroCounting
)

# ── helpers ─────────────────────────────────────────────────────────────────
ok()  { echo -e "  ${GREEN}OK${NC}    $1" | tee -a "$LOGFILE"; }
fail(){ echo -e "  ${RED}FAIL${NC}  $1" | tee -a "$LOGFILE"; }
warn(){ echo -e "  ${YELLOW}WARN${NC}  $1" | tee -a "$LOGFILE"; }
info(){ echo -e "  ${BOLD}INFO${NC}  $1" | tee -a "$LOGFILE"; }

# ── build one package ───────────────────────────────────────────────────────
build_one() {
    local pkg="$1"
    info "Building ${pkg} ..."
    local tmpout
    tmpout=$(lake build "$pkg" 2>&1) && {
        ok "lake build ${pkg}"
    } || {
        fail "lake build ${pkg}"
        echo "$tmpout" | tail -20 | tee -a "$LOGFILE"
        return 1
    }
    return 0
}

# ── compile one .live.lean file ─────────────────────────────────────────────
compile_one_live() {
    local pkg="$1"
    local livefile="${pkg}/${pkg}Live/${pkg}.live.lean"
    if [ ! -f "$livefile" ]; then
        warn "${livefile} not found"
        return 1
    fi
    info "Compiling ${livefile} ..."
    local tmpout
    tmpout=$(lake env lean "$livefile" 2>&1) && {
        ok "live  ${pkg}"
    } || {
        fail "live  ${pkg}"
        echo "$tmpout" | head -10 | tee -a "$LOGFILE"
        return 1
    }
    return 0
}

# ── compile one .web.lean file ──────────────────────────────────────────────
compile_one_web() {
    local pkg="$1"
    local webfile="${pkg}/${pkg}Live/${pkg}.web.lean"
    if [ ! -f "$webfile" ]; then
        info "web   ${pkg} (no .web.lean, skipped)"
        return 2
    fi
    info "Compiling ${webfile} ..."
    local tmpout
    tmpout=$(lake env lean "$webfile" 2>&1) && {
        ok "web   ${pkg}"
    } || {
        fail "web   ${pkg}"
        echo "$tmpout" | head -10 | tee -a "$LOGFILE"
        return 1
    }
    return 0
}

# ── summary counters ────────────────────────────────────────────────────────
BUILD_OK=0;  BUILD_FAIL=0
LIVE_OK=0;   LIVE_FAIL=0
WEB_OK=0;    WEB_FAIL=0;    WEB_SKIP=0

# ── mode: build ─────────────────────────────────────────────────────────────
do_build() {
    local pkgs=("${ALL_PKGS[@]}")
    if [ $# -gt 0 ]; then
        pkgs=("$@")
    fi
    echo "" | tee -a "$LOGFILE"
    echo "── lake build ───────────────────────────────────────────────────────────────" | tee -a "$LOGFILE"
    for pkg in "${pkgs[@]}"; do
        if build_one "$pkg"; then
            ((BUILD_OK++)) || true
        else
            ((BUILD_FAIL++)) || true
        fi
    done
}

# ── mode: live ──────────────────────────────────────────────────────────────
do_live() {
    local pkgs=("${ALL_PKGS[@]}")
    if [ $# -gt 0 ]; then
        pkgs=("$@")
    fi
    echo "" | tee -a "$LOGFILE"
    echo "── .live.lean compilation ───────────────────────────────────────────────────" | tee -a "$LOGFILE"
    for pkg in "${pkgs[@]}"; do
        if compile_one_live "$pkg"; then
            ((LIVE_OK++)) || true
        else
            ((LIVE_FAIL++)) || true
        fi
    done
}

# ── mode: web ───────────────────────────────────────────────────────────────
do_web() {
    local pkgs=("${ALL_PKGS[@]}")
    if [ $# -gt 0 ]; then
        pkgs=("$@")
    fi
    echo "" | tee -a "$LOGFILE"
    echo "── .web.lean compilation (v4.33.0-rc1) ──────────────────────────────────────" | tee -a "$LOGFILE"
    for pkg in "${pkgs[@]}"; do
        local rc=0
        compile_one_web "$pkg" || rc=$?
        if [ $rc -eq 0 ]; then
            ((WEB_OK++)) || true
        elif [ $rc -eq 2 ]; then
            ((WEB_SKIP++)) || true
        else
            ((WEB_FAIL++)) || true
        fi
    done
}

# ── summary ─────────────────────────────────────────────────────────────────
print_summary() {
    {
        echo ""
        echo "=============================================================================="
        echo " SUMMARY"
        echo "=============================================================================="
        if [ $BUILD_OK -gt 0 ] || [ $BUILD_FAIL -gt 0 ]; then
            echo "  lake build : ${BUILD_OK} OK, ${BUILD_FAIL} FAIL"
        fi
        if [ $LIVE_OK -gt 0 ] || [ $LIVE_FAIL -gt 0 ]; then
            echo "  .live.lean : ${LIVE_OK} OK, ${LIVE_FAIL} FAIL"
        fi
        if [ $WEB_OK -gt 0 ] || [ $WEB_FAIL -gt 0 ] || [ $WEB_SKIP -gt 0 ]; then
            echo "  .web.lean  : ${WEB_OK} OK, ${WEB_FAIL} FAIL, ${WEB_SKIP} SKIP"
        fi
        echo ""
        echo "  Log saved to: ${LOGFILE}"
        echo "=============================================================================="
    } | tee -a "$LOGFILE"
}

# ── main dispatcher ─────────────────────────────────────────────────────────
log_header "$@"

case "${1:-all}" in
    all)
        shift
        do_build "$@"
        do_live "$@"
        do_web "$@"
        print_summary
        ;;
    build)
        shift
        do_build "$@"
        print_summary
        ;;
    live)
        shift
        do_live "$@"
        print_summary
        ;;
    web)
        shift
        do_web "$@"
        print_summary
        ;;
    clean)
        info "Removing M4TH.log ..."
        rm -f "$LOGFILE"
        ok "M4TH.log removed"
        ;;
    *)
        echo "Usage: $0 {all|build|live|web|clean} [PackageName ...]"
        exit 1
        ;;
esac

# Exit non-zero if any failures
if [ $((BUILD_FAIL + LIVE_FAIL + WEB_FAIL)) -gt 0 ]; then
    exit 1
fi
exit 0
