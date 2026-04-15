local function fallback(value)
    return "[" .. tostring(value) .. "]"
end

local function choose(n, value)
    return n <= 10 and value or fallback(value)
end

print("take_string", choose(3, "ok"))
print("take_false", choose(3, false))
print("fallback_cmp", choose(20, "ok"))
print("fallback_nil", choose(20, nil))
