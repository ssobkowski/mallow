local outer = 0

while outer < 3 do
    outer = outer + 1
    print("while-start", outer)

    local inner = 0
    local sum = 0

    repeat
        inner = inner + 1
        sum = sum + inner
        print("repeat-inner", outer, inner, sum)
    until inner >= 2

    print("while-end", outer, sum)
end

print("done", outer)
