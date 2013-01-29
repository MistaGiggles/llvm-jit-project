for i in *.a
do
echo "===================================="
echo "LOCAL_MODULE := " $i | sed 's/..$//'
echo "LOCAL_SRC_FILES := " $i
echo "LOCAL_EXPORT_C_INCLUDES := include/"
echo "include \$(PREBUILT_STATIC_LIBRARY)"
echo "===================================="
echo ""
echo ""
done