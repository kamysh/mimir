#!/usr/bin/env bash
# Build an allowlisted environment without inheriting deployment credentials.
isolated_environment() {
    local root=$1 key
    child_env=()
    for key in PATH LANG LC_ALL SSL_CERT_FILE NIX_SSL_CERT_FILE LD_LIBRARY_PATH LIBRARY_PATH PKG_CONFIG_PATH PKG_CONFIG_LIBDIR OPENSSL_DIR OPENSSL_LIB_DIR OPENSSL_INCLUDE_DIR RUST_SRC_PATH NIX_CFLAGS_COMPILE NIX_LDFLAGS NIX_CC NIX_BINTOOLS; do
        [[ ! -v $key ]] || child_env+=("$key=${!key}")
    done
    child_env+=("CARGO_HOME=${CARGO_HOME:-${HOME:?}/.cargo}" "HOME=$root/home" "XDG_CONFIG_HOME=$root/config"
        "XDG_STATE_HOME=$root/state" "XDG_CACHE_HOME=$root/cache" "TMPDIR=$root/scratch"
        "CARGO_TARGET_DIR=$root/target" "MIMIR_EVAL_TARGET_DIR=$root/eval-target" 'CARGO_BUILD_JOBS=4' 'CI=true'
        "PATH=$root/bin:${PATH:?}")
}

owned_container() {
    local id=$1 label=$2 token=$3 json=$4
    [[ $(jq -r '.[0].Id // empty' <<< "$json") == "$id" && $(jq -r --arg key "$label" '.[0].Config.Labels[$key] // empty' <<< "$json") == "$token" ]]
}
