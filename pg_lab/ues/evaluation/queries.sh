# determine current database mode

config="set ues.enable_ues=on; \n show ues.enable_ues;\n"

# number of iterations per experiment
iterations=$1
eval_dir=$2 #has to be the evaluation folder

# checks if folder with prepared queries already exists
# creates folder if not present
if [ ! -d $eval_dir/queries-prep ]; then
	mkdir $eval_dir/queries-prep
fi

# check if output path defined in prepared sql file exists
if [ ! -d $eval_dir/queries-outp/ ]; then
	mkdir $eval_dir/queries-outp
fi

# execute queries is random order
# run every experiment multiple times
for ((curr_iter=0; curr_iter < $iterations; curr_iter++)); do
	# following code is done one time per iteration

	# check if target folder is existing before preapering the sql scripts
	if [ ! -d $eval_dir/queries-outp/$curr_iter ]; then
		mkdir $eval_dir/queries-outp/$curr_iter
	fi

	# prepare sql scripts for execution by defining an output file and defining print stats
	cd $eval_dir/queries
	for file in *.sql; do 
		printf "$config\n\o $eval_dir/queries-outp/$curr_iter/$file.json \nEXPLAIN(Analyze, Format JSON) \n" | cat - $file > tmp &&
		mv tmp ../queries-prep/$file &&
		echo "$file prepared"
	done

	# iterate over alls queries
	cd $eval_dir/queries-prep
	echo -n "mode: $mode | iteration: $curr_iter\n"

	for file in $(ls *.sql); do

		# cover debug option
		# runs only one query
		#if [ "${file}" != "1a.sql" ] && [ "${3}" == "debug" ]; then
		#	continue
		#fi
		
		# execute sql query
		$eval_dir/../../../postgres-server/dist/bin/psql imdb -f $eval_dir/queries-prep/$file
	done

	# reset path
	#cd ../../

done

rm $eval_dir/tmp

exit