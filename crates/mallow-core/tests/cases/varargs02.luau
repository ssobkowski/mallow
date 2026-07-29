local function pack_it(...)
    return { ... }
end

local t = pack_it(10, 20, 30)
print(t[1])
print(t[2])
print(t[3])
print(#t)
