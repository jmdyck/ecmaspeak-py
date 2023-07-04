
class E_Value: # ECMAScript value
    def isan(self, type):
        return isinstance(self, type)

class EL_Value(E_Value): # ECMAScript language value
    pass

class ES_Value(E_Value): # ECMAScript specification value
    pass

# vim: sw=4 ts=4 expandtab
