local function make_tracker(seed)
    local function add(delta)
        seed += delta
        return seed
    end

    local function read(seed)
        return seed, add(0)
    end

    return add, read
end

local add, read = make_tracker(10)

print(read(100))
print(add(5))
print(read(-1))
print(add(-3))
print(read(7))
