def print_item:
    ["Code  \(.lines.code)", "Definitions  \(.definitions)", "Theorems  \(.theorems)"] | join("\t");

def print_language:
    map(print_item) | map("  " + .) | join("\n");

["Source", (.[""] | print_language), "Target", (.["F⊗⊕ω"] | print_language)] | join("\n")