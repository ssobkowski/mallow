local value = {}
local metatable = {
    __index = function()
        return "resolved"
    end,
}

setmetatable(value, metatable)
local resolved = value.name
print(resolved)
print(resolved)
