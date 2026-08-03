local function mixed(value, condition)
    if condition then
        return value
    end
    return 1
end
local function numeric(value)
    local _unused = value + 1
    return value
end
print(mixed("x", true), numeric(2))
