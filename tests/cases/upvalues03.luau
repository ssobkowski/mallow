local function make_counter(seed)
    local value = seed

    return function(step)
        value += step
        return value
    end
end

local first = make_counter(0)
local second = make_counter(100)

print(first(1))
print(first(2))
print(second(5))
print(first(3))
print(second(10))
