/**
 * Excepcion que se lanza cuando se intenta eliminar un elemento que no 
 * pertenece al conjunto o afin.
 * @author victor
 */
public class ExcepcionElementoNoPertenece extends Exception {
    String mensaje;
	
    public ExcepcionElementoNoPertenece (String causa){
        mensaje = causa;
    }
	
    public String gerMessage ()
    {
        return mensaje;
    }
}
