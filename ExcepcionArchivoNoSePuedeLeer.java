/**
 *
 * @author victor
 */
public class ExcepcionArchivoNoSePuedeLeer extends Exception {
    
    String mensaje;
    
    /**
     * Creates a new instance of <code>ExcepcionArchivoNoSePuedeLeer</code> without detail message.
     */
    public ExcepcionArchivoNoSePuedeLeer() {
        mensaje = "El archivo pasado no es legible...";
    }


    /**
     * Constructs an instance of <code>ExcepcionArchivoNoSePuedeLeer</code> with the specified detail message.
     * @param msg the detail message.
     */
    public ExcepcionArchivoNoSePuedeLeer(String msg) {
        super(msg);
        mensaje = msg;
    }
    
    public String gerMessage ()
    {
        return mensaje;
    }
}
