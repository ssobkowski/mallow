local value = 1

local function clear_after_check()
    local function clear()
        value = nil
    end

    if value then
        clear()
        return value
    end

    return 0
end

print(clear_after_check())
