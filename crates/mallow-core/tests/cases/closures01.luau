local fib
fib = function(n)
    if n <= 1 then return n end
    return fib(n - 1) + fib(n - 2)
end

print(fib(10))
