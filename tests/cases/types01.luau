local function returnsMultiple(...): (number, number, number)
  print(... :: string) -- "x"
  return 1, 2, 3
end

print(returnsMultiple("x", "y", "z")) -- 1, 2, 3
print(returnsMultiple("x", "y", "z") :: number) -- 1
