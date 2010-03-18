/* 
 * Archivo: ExcepcionPalabraYaRegistrada.java
 * Autor: Diego Mosquera
 * Fecha: 05-02-10
 *
 */
public class ExcepcionPalabraYaRegistrada extends Exception {
    String mensaje;
	
    public ExcepcionPalabraYaRegistrada (String causa) {
        mensaje = causa;
    }
	
    public String gerMessage () {
        return mensaje;
    }
}