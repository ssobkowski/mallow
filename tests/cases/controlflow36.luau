local flags = { bar = 1 }

local function run()
    flags.foo = true
    while flags.foo do
        local x = flags.bar
        if x then
            flags.foo = false
            flags.bar += 1
        end
    end
end

run()

print(flags.foo, flags.bar)
