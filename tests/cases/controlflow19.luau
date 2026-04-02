local outer = 0

repeat
    outer = outer + 1
    local inner = 0

    repeat
        inner = inner + 1
        print("inner", outer, inner)
    until inner >= 2

    print("outer", outer)
until outer >= 3

print("done", outer)
