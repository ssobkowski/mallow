local function foo(s, x)
    local substring = string.sub(s, 2, 8)
    local d = math.abs(x)
    return substring, d
end
