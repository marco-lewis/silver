for file in Silq_Programs/*
do
if [[ $file == *.slq ]]
then
    ./get_ast.sh $file
fi
done