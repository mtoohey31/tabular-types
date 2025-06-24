def print_item:
    ["Code  \(.lines.code)", "Definitions  \(.definitions)", "Theorems  \(.theorems)"] | join("\t");

def print_language:
    map(print_item) | map("  " + .) | join("\n");

def h: tostring | [while(length>0; .[:-3]) | .[-3:]] | reverse | join("\\,");

def print_number:
    if . == 0 then "/" else . | h end;

def total(sel):
    . | map(map(sel) | add) | add;

[
    "\\midrule",
    "\\multicolumn{5}{l}{\\textbf{Source Language (\\source)}} \\\\", 
    "\\quad Syntax & Kinds, types, terms, programs, and environments & \(.[""].Syntax.lines.code | print_number) & \(.[""].Syntax.definitions | print_number) & \(.[""].Syntax.theorems | print_number) \\\\",
    "\\quad Semantics & Kinding, typing, constraint solving, elaboration, etc. & \(.[""].Semantics.lines.code | print_number) & \(.[""].Semantics.definitions | print_number) & \(.[""].Semantics.theorems | print_number) \\\\",
    "\\quad Lemmas & Auxiliary lemmas and properties & \(.[""].Lemmas.lines.code | print_number) & \(.[""].Lemmas.definitions | print_number) & \(.[""].Lemmas.theorems | print_number) \\\\",
    "\\quad Theorems & Elaboration soundness & \(.[""].Theorems.lines.code | print_number) & \(.[""].Theorems.definitions | print_number) & \(.[""].Theorems.theorems | print_number) \\\\",
    "\\quad Others & & \(.[""].Others.lines.code | print_number) & \(.[""].Others.definitions | print_number) & \(.[""].Others.theorems | print_number) \\\\",
    "\\midrule",
    "\\multicolumn{5}{l}{\\textbf{Target Language (\\Fxpo)}} \\\\",
    "\\quad Syntax & Kinds, types, terms, and environments & \(.["F⊗⊕ω"].Syntax.lines.code | print_number) & \(.["F⊗⊕ω"].Syntax.definitions | print_number) & \(.["F⊗⊕ω"].Syntax.theorems | print_number) \\\\",
    "\\quad Semantics & Kinding, typing, and operational semantics & \(.["F⊗⊕ω"].Semantics.lines.code | print_number) & \(.["F⊗⊕ω"].Semantics.definitions | print_number) & \(.["F⊗⊕ω"].Semantics.theorems | print_number) \\\\",
    "\\quad Lemmas & Auxiliary lemmas and properties & \(.["F⊗⊕ω"].Lemmas.lines.code | print_number) & \(.["F⊗⊕ω"].Lemmas.definitions | print_number) & \(.["F⊗⊕ω"].Lemmas.theorems | print_number) \\\\",
    "\\quad Theorems & Syntactic type safety & \(.["F⊗⊕ω"].Theorems.lines.code | print_number) & \(.["F⊗⊕ω"].Theorems.definitions | print_number) & \(.["F⊗⊕ω"].Theorems.theorems | print_number) \\\\",
    "\\quad Others & & \(.["F⊗⊕ω"].Others.lines.code | print_number) & \(.["F⊗⊕ω"].Others.definitions | print_number) & \(.["F⊗⊕ω"].Others.theorems | print_number) \\\\",
    "\\midrule",
    "\\textbf{Total} & & \\textbf{\(total(.lines.code) | print_number)} & \\textbf{\(total(.definitions) | print_number)} & \\textbf{\(total(.theorems) | print_number)} \\\\"
] | join("\n")
