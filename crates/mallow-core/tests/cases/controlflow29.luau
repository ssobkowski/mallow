local function limit(name)
    print("limit", name)
    return ({
        a = 0.99,
        b = 50,
    })[name]
end

local values = {
    {
        k = "none",
        v = nil,
    },
    {
        k = "first",
        v = {
            k = "first-value",
            a = 1,
            b = {
                c = 80,
            },
        },
    },
    {
        k = "second",
        v = {
            k = "second-value",
            a = 0.5,
            b = {
                c = 40,
            },
        },
    },
    {
        k = "third",
        v = {
            k = "third-value",
            a = 0.5,
            b = {
                c = 80,
            },
        },
    },
}

local function pick(item, key)
    print("pick", item.k, key)
    return item.v
end

local function find_value()
    for index = 1, #values do
        local item = pick(values[index], "x")
        if item and item.a < limit("a") and item.b.c > limit("b") then
            return item
        end
        print("miss", index)
    end
    return nil
end

local result = find_value()
print("result", if result then result.k else "nil")
