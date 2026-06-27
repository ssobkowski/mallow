local fallback = {
    answer = 42,
}
local value = setmetatable({}, {
    __index = fallback,
})

local function read(key)
    return value[key]
end

local resolved = read("answer")
print(resolved)
print(resolved)
