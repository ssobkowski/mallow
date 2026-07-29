local count = 0

while true do
    count = count + 1
    print("iteration", count)

    if count >= 5 then
        print("breaking", count)
        break
    end
end

print("done", count)

local search = { 10, 20, 30, 40, 50 }
local index = 1
local found = nil

while true do
    local value = search[index]
    print("checking", index, value)

    if value == 30 then
        found = index
        break
    end

    index = index + 1

    if index > #search then
        print("not-found")
        break
    end
end

print("result", found)
