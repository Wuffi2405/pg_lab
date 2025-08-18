# determine current database mode
#config="LOAD 'ues.so'; set ues.enable_ues=on; \n show ues.enable_ues;\n"
config=""
configA=""

iterations=$1 # number of iterations per experiment
eval_dir=$2 # has to be the evaluation folder
use_ues=$3 # ues yes or no
mode_analyze=$4 # use EXPLAIN statement or not

case $use_ues in
	"ues")
    	#config+="LOAD 'ues.so'; set ues.enable_ues=on; \n show ues.enable_ues;\n"
		echo -n "HAAAAAAAAAALO"
		#configA+="LOAD 'ues.so'; set ues.enable_ues=on; \n set enable_nestloop=off; \n set enable_mergejoin=off;"
		configA+="LOAD 'ues.so'; set ues.enable_ues=on; "
		;;

  	"noues")
	echo -n "TEEEEEEEEEEEEEEEST"
		configA+="test"
		;;

	*)
		echo -n "missing attribute"
		exit
esac

case $mode_analyze in
	analyze)
		config+="\n\o $eval_dir/queries-outp/$curr_iter/$file.json \nEXPLAIN(Analyze, Format JSON) \n"
		;;

	default)
		config+="\n\o $eval_dir/queries-outp/$curr_iter/$file.json \n"
		;;
		
	*)
		echo -n "missing attribute"
		exit
esac

# checks if folder with prepared queries already exists
# creates folder if not present
if [ ! -d $eval_dir/queries-prep ]; then
	mkdir $eval_dir/queries-prep
fi

# check if output path defined in prepared sql file exists
if [ ! -d $eval_dir/queries-outp/ ]; then
	mkdir $eval_dir/queries-outp
fi

# execute queries in random order
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
		config="\n$configA\o $eval_dir/queries-outp/$curr_iter/$file.json \nEXPLAIN(Analyze, Format JSON) \n"
		
		printf "$config\n" | cat - $file > tmp &&
		mv tmp $eval_dir/queries-prep/$file &&
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

#rm $eval_dir/tmp

exit