local t = {1, 2, 3}
table.insert(t, 4)
table.insert(t, 2, 99)
print(table.concat(t, ","))

local removed = table.remove(t)
print(removed)
print(table.concat(t, ","))

local removed2 = table.remove(t, 2)
print(removed2)
print(table.concat(t, ","))

local nums = {5, 2, 8, 1, 9}
table.sort(nums)
print(table.concat(nums, " "))

local mt = {
    __index = function(t, k)
        return "default"
    end
}

local proxy = {}
setmetatable(proxy, mt)
print(proxy.anything)
print(proxy.something)

local storage = {}
local mt2 = {
    __newindex = function(t, k, v)
        print("setting", k, "to", v)
        storage[k] = v
    end,
    __index = storage
}

local tracked = {}
setmetatable(tracked, mt2)
tracked.x = 10
tracked.y = 20
print(tracked.x)
print(tracked.y)

local mt3 = {
    __tostring = function(t)
        return "custom: " .. t.value
    end
}
local obj = {value = 42}
setmetatable(obj, mt3)
print(obj)

local mt4 = {secret = "meta"}
local t4 = {}
setmetatable(t4, mt4)
local retrieved = getmetatable(t4)
print(retrieved.secret)
