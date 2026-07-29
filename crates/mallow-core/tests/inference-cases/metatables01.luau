local value = {}
setmetatable(value, {
    __add = function(_, rhs)
        return tostring(rhs)
    end,
})

local function add_one(input)
    return input + 1
end

print(add_one(value))
