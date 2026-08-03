local function read_after_nested_call(value)
    local function make_reader()
        local function read()
            if value then
                print()
                return value
            end

            return 0
        end

        return read()
    end

    return make_reader()
end

print(read_after_nested_call(1), read_after_nested_call(nil))
