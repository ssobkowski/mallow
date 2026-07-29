local function merged(label, a, b, c, d, e)
    local result = a and (b and c or (d or e)) or e
    print(label, result)
end

merged("then_c", true, true, "C", "D", "E")
merged("then_d", true, false, "C", "D", "E")
merged("else_e", false, true, "C", "D", "E")
