
def to_dictionary(obj):
    """Convert a class' attributes to a dictionary.
    This operates on nested attributes.
    """
    if not hasattr(obj,"__dict__"):
        return obj

    result = {}
    for key, val in obj.__dict__.items():
        if key.startswith("_"):
            continue
        element = []
        if isinstance(val, list):
            for item in val:
                element.append(to_dictionary(item))
        else:
            element = to_dictionary(val)
        result[key] = element
    return result
