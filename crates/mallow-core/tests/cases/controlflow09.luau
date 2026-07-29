for row = 1, 4 do
    if row % 2 == 0 then
        print("skip-row", row)
        continue
    end

    local row_total = 0

    for column = 1, 5 do
        if column == 4 then
            print("break-at", row, column)
            break
        end

        row_total = row_total + row * column
    end

    print("row-total", row, row_total)
end
