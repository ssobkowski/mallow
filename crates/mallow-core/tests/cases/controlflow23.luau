local outer = 0

repeat
    outer = outer + 1
    print("repeat-start", outer)

    local inner = 0
    local product = 1

    while inner < 3 do
        inner = inner + 1
        product = product * 2
        print("while-inner", outer, inner, product)
    end

    print("repeat-end", outer, product)
until outer >= 2

print("done", outer)
