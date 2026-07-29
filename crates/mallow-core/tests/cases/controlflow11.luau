local values = { "keep", "skip", "stay", "stop", "after" }
local kept = {}

for index, value in ipairs(values) do
    if value == "skip" then
        print("skip", index)
        continue
    end

    if value == "stop" then
        print("stop", index)
        break
    end

    table.insert(kept, value .. index)
end

print(table.concat(kept, ","))
