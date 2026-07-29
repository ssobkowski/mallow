local function id(value)
    print(value)
    local alias = value
    return alias
end
local number_value = id(1)
local string_value = id("x")
print(number_value + 1, string.upper(string_value))
