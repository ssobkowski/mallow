local function read_after_call(value)
    local function read()
        if value then
            print()
            return value
        end

        return 0
    end

    return read()
end

print(read_after_call(1), read_after_call(nil))
