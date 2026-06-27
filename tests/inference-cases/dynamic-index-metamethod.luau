local value = setmetatable({}, {
    __index = function()
        return "resolved"
    end,
})

local resolved = value[1]
print(resolved)
print(resolved)
