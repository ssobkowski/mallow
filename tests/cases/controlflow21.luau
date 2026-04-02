local counter = 10

print("before-loop", counter)

while counter < 5 do
    counter = counter + 1
    print("inside-loop", counter)
end

print("after-loop", counter)

local flag = false

while flag do
    print("unreachable")
end

print("done", flag)
