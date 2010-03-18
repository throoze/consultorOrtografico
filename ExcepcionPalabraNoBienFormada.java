/**
 * Excepcion que indica que la palabra pasada no esta bien formada; esto es:
 * La palabra pasada no es vacia ("") y cada caracter que la conforma es una le-
 * tra minuscula del alfabeto [a..z] exceptuando el caracter "ñ" (alfabeto mi-
 * nusculo ingles).
 * @author Victor De Ponte, carnet 05-38087
 * @author Jose Zabala, carnet 05-39070
 */
class ExcepcionPalabraNoBienFormada extends Exception {
    
    String mensaje;
	
    public ExcepcionPalabraNoBienFormada (String causa)
	{
	    mensaje = causa;
	}
	
	public String gerMessage ()
	{
	    return mensaje;
	}
}