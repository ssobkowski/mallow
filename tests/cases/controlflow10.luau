local seen = {}

for i = 10, -4, -3 do
    if i < 2 then
        print("break", i)
        break
    end

    table.insert(seen, i)
end

print(table.concat(seen, ","))
