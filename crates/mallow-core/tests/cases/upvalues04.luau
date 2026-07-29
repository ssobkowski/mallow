local function make_tracker(seed)
    local value = seed

    local function add(delta)
        value += delta
        return value
    end

    local function read()
        return value
    end

    return add, read
end

local add, read = make_tracker(3)

for i = 1, 4 do
    if i % 2 == 0 then
        print("even", add(i * 10), read())
    else
        print("odd", add(i), read())
    end
end
