local function nested(label, a, b, c, d, e)
    local value = a and (b and c or d) or e
    print(label, value)
end

nested("c_path", true, true, "C", "D", "E")
nested("d_from_b", true, false, "C", "D", "E")
nested("d_from_c", true, true, false, "D", "E")
nested("e_from_a", false, true, "C", "D", "E")
nested("e_from_d", true, true, nil, false, "E")
