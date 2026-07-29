local total = 10

local function add(delta)
    total += delta
    return total
end

local function read()
    return total
end

print(read())
print(add(5))
print(read())
print(add(-3))
print(read())
