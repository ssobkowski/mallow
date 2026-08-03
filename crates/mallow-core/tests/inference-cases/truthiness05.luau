local function observe_after_call(value)
    local function observe()
        return value
    end

    if value then
        observe()
        return value
    end

    return 0
end

print(observe_after_call(1), observe_after_call(nil))
