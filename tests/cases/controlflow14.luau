local outer = 0

while outer < 3 do
    outer = outer + 1
    local inner = 0

    while inner < 2 do
        inner = inner + 1
        print("nested", outer, inner)
    end

    print("outer", outer)
end

print("done", outer)
