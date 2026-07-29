local function make_pair(seed)
    local function read(delta)
        return seed + delta
    end

    local function bump(delta)
        seed += delta
        return seed
    end

    return read, bump
end

local read, bump = make_pair(10)

print(read(5))
print(bump(3))
print(read(-2))
print(bump(-4))
print(read(7))
