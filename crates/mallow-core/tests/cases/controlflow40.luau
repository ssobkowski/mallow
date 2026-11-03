local function last_key(t)
    local key = "none"
    for k in pairs(t) do
        key = k
    end
    return key
end

local function count(t)
    local n = 0
    for _ in ipairs(t) do
        n += 1
    end
    return n
end

local function flag(t)
    local seen = false
    for _, v in next, t do
        seen = true
    end
    return seen
end

local callback = select(1, last_key) -- black box
print(callback({}), callback({ a = 1 }))
print(count({}), count({ 1, 2, 3 }))
print(flag({}), flag({ 1 }))
