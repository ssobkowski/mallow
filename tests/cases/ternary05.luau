local function nested_if(label, a, b, c, d, e)
    local value = if a then (if b then c else d) else e
    print(label, value)
end

nested_if("false_then", true, true, false, "D", "E")
nested_if("nil_else", true, false, "C", nil, "E")
nested_if("outer_else", false, true, "C", "D", "E")
