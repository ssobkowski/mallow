local count = 0
repeat
    count += 1
    local doubled = count * 2
until doubled >= 8  -- doubled is in scope here, NOT outside

print(count)
