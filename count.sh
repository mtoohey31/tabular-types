#!/usr/bin/env bash

# This script counts the number of lines of code, theorems, and lemmas in the project.
# External dependencies: tokei, rg, jq

set -euo pipefail
IFS=$'\t\n'
shopt -s globstar
shopt -s nullglob

CLASSIFICATIONS=("Syntax" "Semantics" "Lemmas" "Theorems")
LANGUAGES=("F⊗⊕ω" "")
ROOT_DIR=$(dirname "$(realpath "$0")")/TabularTypeInterpreter

function append_files() {
    local -n result_array=$1
    local root_dir=$2
    local base_dir=$3
    local classification=$4

    local main_file="${root_dir}/${base_dir}${classification}.lean"
    local glob_pattern=("${root_dir}/${base_dir}${classification}"/**/*.lean)

    if [[ -f "$main_file" ]]; then
        result_array+=("$main_file")
    fi
    result_array+=("${glob_pattern[@]}")
}

JQ_REPORT='["Comments  ", .Lean.comments, "\tCode  ", .Lean.code, "\tBlanks  ", .Lean.blanks, "\tTotal  ", .Lean.blanks + .Lean.comments + .Lean.code] | join("")'

function count_language() {
    local language=$1
    local base_dir
    if [ "$language" != "" ]; then
        base_dir="${language}/"
    else
        base_dir=""
    fi

    for classification in "${CLASSIFICATIONS[@]}"; do
        echo -ne "\n[${language}] ${classification}\t"

        local files=()
        append_files files "$ROOT_DIR" "$base_dir" "$classification"

        if [[ ${#files[@]} -gt 0 ]]; then
            tokei "${files[@]}" -o json | jq -j "$JQ_REPORT"
            echo -ne "\tDefinitions "
            rg -q --stats --json "^def |^judgement |^nonterminal " "${files[@]}" | jq -j ".data.stats.matches" || true
            echo -ne "\tTheorems  "
            rg -q --stats --json "^theorem|^lemma" "${files[@]}" | jq -j ".data.stats.matches" || true
        else
            echo "No files found for ${classification}"
        fi
    done

    local files=("$ROOT_DIR/$base_dir"**/*.lean)
    local excludes=()
    for classification in "${CLASSIFICATIONS[@]}"; do
        append_files excludes "$ROOT_DIR" "$base_dir" "$classification"
    done
    
    if [ "$language" == "" ]; then
        for other_language in "${LANGUAGES[@]}"; do
            if [ "$other_language" != "" ]; then
                local other_base_dir="${other_language}/"
                excludes+=("$ROOT_DIR/$other_base_dir"**/*.lean)
            fi
        done
    fi

    local filtered_files=()
    for file in "${files[@]}"; do
        local exclude_found=false
        for exclude in "${excludes[@]}"; do
            if [[ "$file" == "$exclude" ]]; then
                exclude_found=true
                break
            fi
        done
        if [[ "$exclude_found" == false ]]; then
            filtered_files+=("$file")
        fi
    done

    echo -ne "\n[${language}] Others\t"
    if [[ ${#filtered_files[@]} -gt 0 ]]; then
        tokei "${filtered_files[@]}" -o json | jq -j "$JQ_REPORT"
        echo -ne "\tDefinitions "
        rg -q --stats --json "^def |^judgement |^nonterminal " "${filtered_files[@]}" | jq -j ".data.stats.matches" || true
        echo -ne "\tTheorems  "
        rg -q --stats --json "^theorem|^lemma" "${filtered_files[@]}" | jq -j ".data.stats.matches" || true
    else
        echo "No other files found"
    fi
}

for language in "${LANGUAGES[@]}"; do
    count_language "${language}"
done
