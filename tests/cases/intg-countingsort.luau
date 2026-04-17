local counting = {}

function counting.sort(array)
	local k = math.max(unpack(array))
	local bucket = {}
	local count = {}

	for i = 0, k do
		count[i] = 0
	end

	for j = 1, #array do
		count[array[j]] = count[array[j]] + 1
	end

	for i = 1, k do
		count[i] = count[i] + count[i - 1]
	end

	for j = #array, 1, -1 do
		bucket[count[array[j]]] = array[j]
		count[array[j]] = count[array[j]] - 1
	end

	for i = 1, #array do
		array[i] = bucket[i]
	end

	return array
end

local nums = {290, 614, 925, 375, 187, 581, 148, 550, 116, 339, 685, 997, 236, 264, 250, 642, 809, 367, 615, 489, 207, 641, 424, 298, 880, 700, 452, 398, 938, 327, 967, 632, 254, 821, 744, 393, 411, 592, 464, 186, 590, 595, 301, 238, 198, 419, 979, 434, 326, 832, 126, 107, 241, 930, 506, 503, 674, 374, 106, 268, 431, 965, 229, 500, 980, 355, 220, 178, 747, 413, 471, 387, 869, 109, 862, 557, 675, 793, 313, 696, 114, 908, 120, 135, 555, 757, 889, 294, 494, 369, 391, 428, 887, 955, 811, 343, 531, 790, 637, 718}
print(table.concat(nums, ","))

counting.sort(nums)
print(table.concat(nums, ","))
