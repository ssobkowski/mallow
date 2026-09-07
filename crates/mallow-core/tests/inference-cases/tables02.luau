local function passthrough(value)
    return value
end

local record = {
    value = 42,
}

local function construct(index)
    local dynamic = {
        [passthrough(index)] = "value",
    }
    return dynamic[index]
end

local function choose(flag)
    local key = if flag then "left" else "right"
    return {
        [key] = 2,
        left = 3,
    }
end

local indexed = construct(1)
local choice = choose(true)
print(record.value, indexed, choice)
